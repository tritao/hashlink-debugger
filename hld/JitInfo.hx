package hld;

private typedef FunctionSourceSpan = { var file : String; var line : Int; var column : Int; var endLine : Int; var endColumn : Int; var sourceHash : Int; var start : Int; var end : Int; var flags : Int; }
private typedef JitFunctionMapping = { var stableId : Int; var start : Pointer; var large : Bool; var offsets : haxe.io.Bytes; @:optional var vars : haxe.io.Bytes; @:optional var sourceSpans : Array<FunctionSourceSpan>; }

private enum DebugFlag {
	Is64; // runs in 64 bit mode
	Bool4; // bool = 4 bytes (instead of 1)
	Threads; // was compiled with threads support
	IsWinCall;
}

class JitInfo {

	public var is64(default, null) : Bool;
	public var isWinCall(default, null) : Bool;
	public var align(default,null) : Align;
	public var hasThreads(get,never) : Bool;
	public var pid(default,null) : Int = 0;
	public var protocolVersion(default,null) : Int = 0;
	public var moduleRevision(default,null) : Int = 0;
	public var moduleIdentity(default,null) : Pointer;
	public var debugModules(default,null) : Array<JitInfo> = [];

	var flags : haxe.EnumFlags<DebugFlag>;
	var input : haxe.io.Input;

	public var oldThreadInfos : { id : Int, stackTop : Pointer, debugExc : Pointer };

	public var trampoline(default,null) : Null<{ marker : Pointer, regsOffset : Int, rbpOffset : Int, callOffset : Int, regs : Array<Eval.NativeReg> }>;
	var trampolinePos : Int = -1;

	public var hlVersion : Float;
	public var globals : Pointer;
	var codeStart : Pointer;
	var codeEnd : Pointer;
	public var threads : Pointer;
	var codeSize : Int;
	var allTypes : Pointer;

	var functions : Array<JitFunctionMapping>;
	var baseFunctions : Array<JitFunctionMapping>;
	var functionByCodePos : Int64Map<Int>;
	public var module(default,null) : Module;
	var codeRanges : Array<{ start : Pointer, end : Pointer }> = [];

	public function new() {
	}

	function get_hasThreads() {
		return oldThreadInfos != null || flags.has(Threads);
	}

	private function readPointer() : Pointer {
		if( is64 )
			return Pointer.make(input.readInt32(), input.readInt32());
		return Pointer.make(input.readInt32(),0);
	}

	function readStructSizes() {
		var structSizes = [0];
		for( i in 1...9 )
			structSizes[i] = input.readInt32();
		for( i in 9...HGUID.getIndex() + 1 )
			structSizes[i] = structSizes[HBytes.getIndex()];
		structSizes[HGUID.getIndex()] = structSizes[HI64.getIndex()];
		@:privateAccess align.structSizes = structSizes;
	}

	public function read( input : haxe.io.Input, module : Module ) {
		this.input = input;
		this.module = module;

		if( input.readString(3) != "HLD" )
			return false;
		var version = input.readByte() - "0".code;
		protocolVersion = version;
		if( version <= 0 || version > 3 )
			return false;
		flags = haxe.EnumFlags.ofInt(input.readInt32());
		is64 = flags.has(Is64);
		align = new Align(is64, flags.has(Bool4)?4:1);
		isWinCall = flags.has(IsWinCall) || Sys.systemName() == "Windows" /* todo : disable this for cross platform remote debug */;

		var ver = input.readInt32();
		hlVersion = (ver >> 16) + ((ver >> 8) & 0xFF) / 100;
		if( hlVersion >= 1.07 )
			pid = input.readInt32();
		threads = readPointer();

		functions = [];

		if( version == 1 ) {

			globals = readPointer();
			codeStart = readPointer();
			codeSize = input.readInt32();
			allTypes = readPointer();

			readStructSizes();

			if( !readModule(true) )
				return false;

		} else {
			readStructSizes();

			trampolinePos = input.readInt32();

			var nmodules = input.readInt32();
			if( nmodules != 1 ) {
				#if hl
				throw "TODO : multiple modules support";
				#end
				return false;
			}

			if( !readModule() )
				return false;
			if( version == 3 && !readPatchMappings() )
				return false;
		}

		return true;
	}

	function readPatchMappings() {
		moduleIdentity = readPointer();
		var bytecodeSize = input.readInt32();
		if( bytecodeSize < 0 ) return false;
		input.read(bytecodeSize); // launch module is already loaded by the adapter
		moduleRevision = input.readInt32();
		globals = readPointer();
		allTypes = readPointer();
		if( !readRefreshBase(module, null) ) return false;
		var regionCount = input.readInt32();
		if( moduleRevision < 1 || regionCount < 0 ) return false;
		for( _ in 0...regionCount ) {
			var regionStart = readPointer();
			var regionSize = input.readInt32();
			var retired = input.readByte() != 0;
			var functionCount = input.readInt32();
			if( regionSize <= 0 || functionCount <= 0 ) return false;
			codeRanges.push({ start : regionStart, end : regionStart.offset(regionSize) });
			for( _ in 0...functionCount ) {
				var functionIndex = input.readInt32();
				if( functionIndex < 0 || functionIndex >= module.code.functions.length ) return false;
				var stableId = input.readInt32();
				if( stableId != module.getStableFunctionId(functionIndex) ) return false;
				var fn = module.code.functions[functionIndex];
				var nops = input.readInt32();
				var start = regionStart.offset(input.readInt32());
				var varsSize = input.readInt32();
				var large = input.readByte() != 0;
				if( nops != fn.debug.length >> 1 || varsSize < 0 ) return false;
				var offsets = input.read((nops + 1) * (large ? 4 : 2));
				var vars = input.read(varsSize);
				var sourceSpans = readSourceSpans(module, nops);
				if( sourceSpans == null ) return false;
				if( !retired ) {
					functions[functionIndex] = {stableId: stableId, start: start, large: large, offsets: offsets, vars: vars, sourceSpans: sourceSpans};
					functionByCodePos.set(start.i64,functionIndex);
				}
			}
		}
		applySourceSpans(this);
		return true;
	}

	/** Read a complete MAP3 frame. Parsing happens into temporary module mappings so
		an incomplete socket chunk never mutates the live address tables. */
	public function readRefresh( input : haxe.io.Input, readHeader = true ) : Bool {
		this.input = input;
		if( readHeader && input.readString(4) != "MAP3" ) return false;
		var count = input.readInt32();
		if( count <= 0 ) return false;
		var parsed = [];
		for( _ in 0...count ) {
			var identity = readPointer();
			var bytecodeSize = input.readInt32();
			if( bytecodeSize < 0 ) return false;
			var bytecode = input.read(bytecodeSize);
			var revision = input.readInt32();
			var moduleGlobals = readPointer();
			var moduleTypes = readPointer();
			if( revision < 1 ) return false;
			var target = findModule(identity);
			var targetModule = target == null ? null : target.module;
			if( targetModule == null ) {
				if( bytecodeSize == 0 ) return false;
				targetModule = new Module();
				targetModule.load(bytecode);
				targetModule.init(align);
			}
			var next = cloneForModule(targetModule, identity, revision);
			next.globals = moduleGlobals;
			next.allTypes = moduleTypes;
			if( !readRefreshBase(targetModule, next) ) return false;
			var regionCount = input.readInt32();
			if( regionCount < 0 ) return false;
			for( _ in 0...regionCount ) {
				var regionStart = readPointer();
				var regionSize = input.readInt32();
				var retired = input.readByte() != 0;
				var functionCount = input.readInt32();
				if( regionSize <= 0 || functionCount <= 0 ) return false;
				next.codeRanges.push({ start : regionStart, end : regionStart.offset(regionSize) });
				for( _ in 0...functionCount ) {
					var functionIndex = input.readInt32();
					if( functionIndex < 0 || functionIndex >= targetModule.code.functions.length ) return false;
					var stableId = input.readInt32();
					if( stableId != targetModule.getStableFunctionId(functionIndex) ) return false;
					var fn = targetModule.code.functions[functionIndex];
					var nops = input.readInt32();
					var start = regionStart.offset(input.readInt32());
					var varsSize = input.readInt32();
					var large = input.readByte() != 0;
					if( nops != fn.debug.length >> 1 || varsSize < 0 ) return false;
					var offsets = input.read((nops + 1) * (large ? 4 : 2));
					var vars = input.read(varsSize);
					var sourceSpans = readSourceSpans(targetModule, nops);
					if( sourceSpans == null ) return false;
					if( !retired ) {
						next.functions[functionIndex] = { stableId: stableId, start: start, large: large, offsets: offsets, vars: vars, sourceSpans: sourceSpans };
						next.functionByCodePos.set(start.i64, functionIndex);
					}
				}
				var snapshotCount = input.readInt32();
				if( snapshotCount < 0 ) return false;
				for( _ in 0...snapshotCount ) {
					var sourceHash = input.readInt32(), length = input.readInt32();
					if( length < 0 || !targetModule.addSourceSnapshot(sourceHash, input.read(length)) ) return false;
				}
			}
			parsed.push(next);
			if( next.codeRanges.length > 0 ) {
				next.codeStart = next.codeRanges[0].start;
				next.codeEnd = next.codeRanges[0].end;
				for( range in next.codeRanges ) if( range.end > next.codeEnd ) next.codeEnd = range.end;
			}
		}
		for( next in parsed ) replaceModule(next);
		return true;
	}

	function readRefreshBase(targetModule:Module, target:Null<JitInfo>) {
		var start = readPointer();
		var size = input.readInt32();
		var count = input.readInt32();
		if( size <= 0 || count != targetModule.code.functions.length ) return false;
		var parsed = [];
		for( index in 0...count ) {
			var fn = targetModule.code.functions[index];
			var stableId = input.readInt32();
			if( stableId != targetModule.getStableFunctionId(index) ) return false;
			var nops = input.readInt32();
			var fnStart = start.offset(input.readInt32());
			var varsSize = input.readInt32();
			var large = input.readByte() != 0;
			if( nops != fn.debug.length >> 1 || varsSize < 0 ) return false;
			var offsets = input.read((nops + 1) * (large ? 4 : 2)), vars = input.read(varsSize), sourceSpans = readSourceSpans(targetModule, nops);
			if( sourceSpans == null ) return false;
			parsed.push({ stableId: stableId, start: fnStart, large: large, offsets: offsets, vars: vars, sourceSpans: sourceSpans });
		}
		if( target != null ) {
			target.codeStart = start;
			target.codeEnd = start.offset(size);
			target.codeSize = size;
			target.baseFunctions = parsed;
			target.functions = parsed.copy();
			target.functionByCodePos = new Int64Map();
			for( index in 0...parsed.length ) target.functionByCodePos.set(parsed[index].start.i64, index);
		}
		return true;
	}

	function readSourceSpans(targetModule:Module, nops:Int):Null<Array<FunctionSourceSpan>> {
		var count = input.readInt32();
		if( count != 0 && count != nops ) return null;
		var spans = [];
		for( _ in 0...count ) {
			var file = input.readInt32(), line = input.readInt32(), column = input.readInt32(), endLine = input.readInt32(), endColumn = input.readInt32(),
				sourceHash = input.readInt32(), start = input.readInt32(), end = input.readInt32(), flags = input.readInt32();
			if( file < 0 || file >= targetModule.code.debugFiles.length || line < 1 || column < 1 || endLine < line || endColumn < 1
				|| endLine == line && endColumn < column || flags < 0
				|| !((start == -1 && end == -1) || (start >= 0 && end >= start)) ) return null;
			spans.push({file:targetModule.code.debugFiles[file], line:line, column:column, endLine:endLine, endColumn:endColumn,
				sourceHash:sourceHash, start:start, end:end, flags:flags});
		}
		return spans;
	}

	function cloneForModule(module:Module, identity:Pointer, revision:Int) {
		var out = new JitInfo();
		out.flags = flags; out.is64 = is64; out.isWinCall = isWinCall; out.align = align;
		out.pid = pid; out.protocolVersion = protocolVersion; out.hlVersion = hlVersion;
		out.threads = threads; out.oldThreadInfos = oldThreadInfos; out.trampoline = trampoline;
		out.module = module; out.moduleIdentity = identity; out.moduleRevision = revision;
		var previous = findModule(identity);
		out.baseFunctions = previous == null ? null : previous.baseFunctions;
		out.functions = out.baseFunctions == null ? [] : out.baseFunctions.copy();
		out.functionByCodePos = new Int64Map();
		for( index in 0...out.functions.length ) {
			var fn = out.functions[index];
			if( fn != null ) out.functionByCodePos.set(fn.start.i64, index);
		}
		return out;
	}

	function findModule(identity:Pointer):JitInfo {
		if( moduleIdentity != null && moduleIdentity == identity ) return this;
		for( item in debugModules ) if( item.moduleIdentity == identity ) return item;
		return null;
	}

	function replaceModule(next:JitInfo) {
		applySourceSpans(next);
		if( moduleIdentity == next.moduleIdentity ) {
			moduleRevision = next.moduleRevision;
			functions = next.functions;
			functionByCodePos = next.functionByCodePos;
			codeRanges = next.codeRanges;
			return;
		}
		for( i in 0...debugModules.length )
			if( debugModules[i].moduleIdentity == next.moduleIdentity ) {
				debugModules[i] = next;
				return;
			}
		debugModules.push(next);
	}

	function applySourceSpans(owner:JitInfo) {
		for( index in 0...owner.functions.length ) {
			var fn = owner.functions[index];
			if( fn != null && fn.sourceSpans != null && fn.sourceSpans.length > 0 ) owner.module.replaceOpcodeSourceSpans(index, fn.sourceSpans);
		}
	}

	function readModule( skipHeader=false ) {

		if( !skipHeader ) {
			globals = readPointer();
			codeStart = readPointer();
			codeSize = input.readInt32();
			allTypes = readPointer();
		}

		var nfunctions = input.readInt32();
		if( nfunctions != module.code.functions.length )
			return false;

		functionByCodePos = new Int64Map();
		for( i in 0...nfunctions ) {
			var nops = input.readInt32();
			if( module.code.functions[i].debug.length >> 1 != nops )
				return false;
			var start = codeStart.offset(input.readInt32());
			var varsSize = hlVersion >= 2 ? input.readInt32() : 0;
			var large = input.readByte() != 0;
			var offsets = input.read((nops + 1) * (large ? 4 : 2));
			var vars = hlVersion >= 2 ? input.read(varsSize) : null;
			functionByCodePos.set(start.i64, i);
			functions.push({
				stableId : module.getStableFunctionId(i),
				start : start,
				large : large,
				offsets : offsets,
				vars : vars,
			});
		}

		codeEnd = codeStart.offset(codeSize);
		baseFunctions = functions.copy();
		if( trampolinePos >= 0 )
			trampoline = makeTrampoline(codeStart.offset(trampolinePos));
		return true;
	}

	static inline var TRAMPOLINE_STACK_ARGS = 32;

	function makeTrampoline( marker : Pointer ) {
		var regs : Array<Eval.NativeReg> = isWinCall ? [Esi, Edi, Ebx, R12, R13, R14, R15] : [Ebx, R12, R13, R14, R15];
		if( isWinCall )
			for( i in 6...16 ) regs.push(Eval.NativeReg.XMM(i));
		var regsSize = regs.length * align.ptr;
		if( regsSize & 15 != 0 ) regsSize += 16 - (regsSize & 15);
		var regsOffset = align.ptr + (isWinCall ? 0x20 : 0) + TRAMPOLINE_STACK_ARGS;
		return {
			marker : marker,
			regsOffset : regsOffset,
			rbpOffset : regsOffset + regsSize,
			callOffset : regsOffset + regsSize + align.ptr,
			regs : regs,
		};
	}

	public function getFunctionVars( fidx : Int ) {
		var fn = functions[fidx];
		return fn == null ? null : fn.vars;
	}

	public inline function hasFunction( fidx:Int ) return functions[fidx] != null;
	public function findFunctionByStableId(stableId:Int):Null<Int> {
		for( index in 0...functions.length ) {
			var fn = functions[index];
			if( fn != null && fn.stableId == stableId ) return index;
		}
		return null;
	}

	public function getFunctionPos( fidx : Int ) : Pointer {
		return functions[fidx].start;
	}

	public function getCodePos( fidx : Int, pos : Int ) : Pointer {
		var dbg = functions[fidx];
		return dbg.start.offset(dbg.large ? dbg.offsets.getInt32(pos << 2) : dbg.offsets.getUInt16(pos << 1));
	}

	public function isCodePtr( codePtr : Pointer ) : Bool {
		for( range in codeRanges ) if( codePtr >= range.start && codePtr <= range.end ) return true;
		for( item in debugModules ) if( item.isCodePtr(codePtr) ) return true;
		if( codeStart == null || codeEnd == null ) return false;
		if( codePtr < codeStart || codePtr > codeEnd )
			return false;
		return true;
	}

	public function getNativeCodePos( codePtr : Pointer ) {
		return codePtr.sub(codeStart);
	}

	public function codePtrToString( codePtr : Pointer ) : String {
		if( codePtr < codeStart || codePtr > codeEnd )
			return '$codePtr';
		return '$codePtr(${codePtr.sub(codeStart)})';
	}

	public function resolveAsmPos( codePtr : Pointer ) : Null<Debugger.StackRawInfo> {
		for( item in debugModules ) {
			var found = item.resolveAsmPos(codePtr);
			if( found != null ) return found;
		}
		if( !isCodePtr(codePtr) )
			return null;
		var fidx = -1;
		var best : Pointer = null;
		for( index in 0...functions.length ) {
			var candidate = functions[index];
			if( candidate != null && candidate.start <= codePtr && (best == null || candidate.start > best) ) {
				fidx = index;
				best = candidate.start;
			}
		}
		if( fidx < 0 ) return null;
		var dbg = functions[fidx];
		var fdebug = module.code.functions[fidx];
		var min = 0;
		var max = fdebug.debug.length>>1;
		var relPos = codePtr.sub(dbg.start);
		while( min < max ) {
			var mid = (min + max) >> 1;
			var offset = dbg.large ? dbg.offsets.getInt32(mid * 4) : dbg.offsets.getUInt16(mid * 2);
			if( offset <= relPos )
				min = mid + 1;
			else
				max = mid;
		}
		return { fidx : fidx, fpos : min - 1, codePos : codePtr, ebp : null, jit : this, module : module };
	}

	public function functionFromAddr( p : Pointer ) {
		return functionByCodePos.get(p.i64);
	}

}
