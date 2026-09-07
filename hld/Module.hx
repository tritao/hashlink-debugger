package hld;
import format.hl.Data;

private typedef GlobalAccess = {
	var sub : Map<String,GlobalAccess>;
	var gid : Null<Int>;
}

typedef ModuleProto = {
	var name : String;
	var size : Int;
	var padSize : Int;
	var largestField : Int;
	var fieldNames : Array<String>;
	var parent : ModuleProto;
	var fields : Map<String,{
		var name : String;
		var t : HLType;
		var offset : Int;
	}>;
	var methods : Map<String,{ t : HLType, index : Int, pindex : Int }>;
}

typedef ModuleEProto = Array<{ name : String, size : Int, params : Array<{ offset : Int, t : HLType }> }>;

class Module {

	public var code : format.hl.Data;
	var fileIndexes : Map<String, Int>;
	var functionsByFile : Map<Int, Array<{ f : HLFunction, ifun : Int, lmin : Int, lmax : Int }>>;
	var globalsOffsets : Array<Int>;
	var globalTable : GlobalAccess;
	var typeCache : Map<String, HLType>;
	var protoCache : Map<String,ModuleProto>;
	var eprotoCache : Map<String,ModuleEProto>;
	var functionRegsCache : Array<Array<{ t : HLType, offset : Int }>>;
	var align : Align;
	var reversedHashes : Map<Int,String>;
	var graphCache : Map<Int, CodeGraph>;
	var methods : Array<{ obj : ObjPrototype, field : String }>;
	var functionIdentities : Array<{ stableId : Int, name : String, displayName : String, ifun : Int, sourcePath : String, start : Int, end : Int, line : Int, flags : Int }>;
	var opcodeSourceSpans : Map<Int,Map<Int,{ sourcePath : String, start : Int, end : Int, line : Int, flags : Int }>>;
	var functionsIndexes : Map<Int,Int>;
	var isWindows : Bool;
	var closureContextId : Int = 0;

	public function new() {
		protoCache = new Map();
		eprotoCache = new Map();
		graphCache = new Map();
		functionsIndexes = new Map();
		functionRegsCache = [];
		methods = [];
		functionIdentities = [];
		opcodeSourceSpans = [];
		isWindows = Sys.systemName() == "Windows";
	}

	public function getMethodContext( fidx : Int ) {
		var f = code.functions[fidx];
		if( f == null ) return null;
		return methods[f.findex];
	}

	public function getNamedFunctions() : Array<{ stableId : Int, name : String, field : String, ifun : Int }> {
		var result = [];
		var explicit = new Map<Int,Bool>();
		for( identity in functionIdentities ) {
			result.push({ stableId : identity.stableId, name : identity.name, field : identity.displayName, ifun : identity.ifun });
			explicit.set(identity.ifun, true);
		}
		for( ifun in 0...code.functions.length ) {
			if( explicit.exists(ifun) ) continue;
			var context = getMethodContext(ifun);
			if( context == null ) continue;
			var objectName = context.obj.name.split("$").join("");
			var field = context.field == "__constructor__" ? "new" : context.field;
			result.push({ stableId : code.functions[ifun].findex, name : objectName + "." + field, field : field, ifun : ifun });
		}
		return result;
	}

	public function getStableFunctionId(ifun:Int):Int {
		for( identity in functionIdentities ) if( identity.ifun == ifun ) return identity.stableId;
		return code.functions[ifun].findex;
	}

	public function getFunctionDebugName(ifun:Int):Null<String> {
		for( identity in functionIdentities ) if( identity.ifun == ifun ) return identity.name;
		return null;
	}

	public function load( data : haxe.io.Bytes ) {
		var version = data.length > 3 ? data.get(3) : 0;
		var readerBytes = data;
		if( version == 7 ) {
			readerBytes = data.sub(0, data.length);
			readerBytes.set(3, 6); // format 3.x does not yet know that v7 only appends sections.
		}
		var input = new haxe.io.BytesInput(readerBytes);
		input.bigEndian = false;
		code = new format.hl.Reader().read(input);

		if( code.debugFiles == null )
			throw "Debug info not available in the bytecode";

		for( t in code.types )
			switch( t ) {
			case HObj(o), HStruct(o):
				for( f in o.proto )
					methods[f.findex] = { obj : o, field : f.name };
				for( b in o.bindings )
					methods[b.mid] = { obj : o, field : fetchField(o, b.fid).name };
			default:
			}

		// init files
		fileIndexes = new Map();
		for( i in 0...code.debugFiles.length ) {
			var f = code.debugFiles[i];
			fileIndexes.set(f, i);
			var low = f.split("\\").join("/").toLowerCase();
			fileIndexes.set(low, i);
			var fileOnly = low.split("/").pop();
			if( !fileIndexes.exists(fileOnly) ) {
				fileIndexes.set(fileOnly, i);
				if( StringTools.endsWith(fileOnly,".hx") )
					fileIndexes.set(fileOnly.substr(0, -3), i);
			}
		}

		functionsByFile = new Map();
		for( ifun in 0...code.functions.length ) {
			var f = code.functions[ifun];
			var files = new Map();
			functionsIndexes.set(f.findex, ifun);
			for( i in 0...f.debug.length >> 1 ) {
				var ifile = f.debug[i << 1];
				var dline = f.debug[(i << 1) + 1];
				var inf = files.get(ifile);
				if( inf == null ) {
					inf = { f : f, ifun : ifun, lmin : 1000000, lmax : -1 };
					files.set(ifile, inf);
					var fl = functionsByFile.get(ifile);
					if( fl == null ) {
						fl = [];
						functionsByFile.set(ifile, fl);
					}
					fl.push(inf);
				}
				if( dline < inf.lmin ) inf.lmin = dline;
				if( dline > inf.lmax ) inf.lmax = dline;
			}
		}
		for( i in 0...code.natives.length )
			functionsIndexes.set(code.natives[i].findex, code.functions.length + i);
		if( version == 7 ) readDebugSections(data, input.position);
	}

	function readDebugSections(data:haxe.io.Bytes, position:Int) {
		var input = new haxe.io.BytesInput(data);
		input.position = position;
		input.bigEndian = false;
		var count = readUnsignedIndex(input);
		var sections = [], seen = new Map<String,Bool>();
		for( _ in 0...count ) {
			var kind = readUnsignedIndex(input);
			var version = readUnsignedIndex(input);
			var flags = readUnsignedIndex(input);
			var length = readUnsignedIndex(input);
			var key = kind + ":" + version;
			if( kind <= 0 || version <= 0 || length > data.length - input.position || seen.exists(key) ) throw "Invalid HLB debug section";
			seen.set(key, true);
			sections.push({kind:kind, version:version, payload:input.read(length)});
		}
		if( input.position != data.length ) throw "Trailing data after HLB debug sections";
		for( section in sections ) if( section.kind == 1 && section.version == 1 ) readFunctionIdentities(section.payload);
		for( section in sections ) if( section.kind == 2 && section.version == 1 ) readOpcodeSourceSpans(section.payload);
	}

	function readFunctionIdentities(bytes:haxe.io.Bytes) {
		var input = new haxe.io.BytesInput(bytes);
		var count = readUnsignedIndex(input);
		var stableIds = new Map<Int,Bool>();
		var functionIds = new Map<Int,Bool>();
		for( _ in 0...count ) {
			var stableId = readUnsignedIndex(input);
			var functionIndex = readUnsignedIndex(input);
			var name = readSizedString(input);
			var displayName = readSizedString(input);
			var sourcePath = readSizedString(input);
			var start = readIndex(input) - 1;
			var end = readIndex(input) - 1;
			var line = readUnsignedIndex(input);
			var flags = readUnsignedIndex(input);
			var ifun = functionsIndexes.get(functionIndex);
			if( ifun == null || ifun >= code.functions.length || name == "" || displayName == "" || stableIds.exists(stableId) || functionIds.exists(functionIndex) )
				throw "Invalid HLB function identity";
			stableIds.set(stableId, true);
			functionIds.set(functionIndex, true);
			functionIdentities.push({stableId:stableId, name:name, displayName:displayName, ifun:ifun, sourcePath:sourcePath, start:start, end:end, line:line, flags:flags});
		}
		if( input.position != input.length ) throw "Trailing data in HLB function identities";
	}

	function readOpcodeSourceSpans(bytes:haxe.io.Bytes) {
		var input = new haxe.io.BytesInput(bytes), files = [];
		for( _ in 0...readUnsignedIndex(input) ) files.push(readSizedString(input));
		var seenFunctions = new Map<Int,Bool>();
		for( _ in 0...readUnsignedIndex(input) ) {
			var stableId = readUnsignedIndex(input), ifun:Null<Int> = null;
			for( identity in functionIdentities ) if( identity.stableId == stableId ) { ifun = identity.ifun; break; }
			if( ifun == null || seenFunctions.exists(stableId) ) throw "Invalid HLB opcode source-span function";
			seenFunctions.set(stableId, true);
			var mappings:Map<Int,{ sourcePath : String, start : Int, end : Int, line : Int, flags : Int }> = [];
			for( _ in 0...readUnsignedIndex(input) ) {
				var opcode = readUnsignedIndex(input), file = readUnsignedIndex(input), start = readIndex(input) - 1,
					end = readIndex(input) - 1, line = readUnsignedIndex(input), flags = readUnsignedIndex(input);
				var validRange = start == -1 && end == -1 || start >= 0 && end >= start;
				if( opcode >= code.functions[ifun].ops.length || file >= files.length || mappings.exists(opcode)
					|| line < 1 || !validRange ) throw "Invalid HLB opcode source span";
				mappings.set(opcode, {sourcePath:files[file], start:start, end:end, line:line, flags:flags});
			}
			opcodeSourceSpans.set(ifun, mappings);
		}
		if( input.position != input.length ) throw "Trailing data in HLB opcode source spans";
	}

	static function readSizedString(input:haxe.io.BytesInput) {
		var length = readUnsignedIndex(input);
		return input.readString(length);
	}

	static function readUnsignedIndex(input:haxe.io.BytesInput) {
		var value = readIndex(input);
		if( value < 0 ) throw "Negative HLB unsigned index";
		return value;
	}

	static function readIndex(input:haxe.io.BytesInput) {
		var b = input.readByte();
		if( b & 0x80 == 0 ) return b & 0x7F;
		if( b & 0x40 == 0 ) {
			var value = input.readByte() | ((b & 31) << 8);
			return b & 0x20 == 0 ? value : -value;
		}
		var value = ((b & 31) << 24) | (input.readByte() << 16) | (input.readByte() << 8) | input.readByte();
		return b & 0x20 == 0 ? value : -value;
	}

	function fetchField( o : ObjPrototype, fid : Int ) {
		var pl = [];
		var fcount = 0;
		while( true ) {
			pl.push(o);
			fcount += o.fields.length;
			if( o.tsuper == null ) break;
			switch( o.tsuper ) {
			case HObj(s): o = s;
			default: throw "assert";
			}
		}
		if( fid < 0 || fid >= fcount )
			return null;
		for( i in 0...pl.length ) {
			var o = pl[pl.length - i - 1];
			if( fid < o.fields.length )
				return o.fields[fid];
			fid -= o.fields.length;
		}
		return null;
	}

	public function init( align : Align ) {
		this.align = align;

		// init globals
		var globalsPos = 0;
		globalsOffsets = [];
		for( g in code.globals ) {
			globalsPos += align.padSize(globalsPos, g);
			globalsOffsets.push(globalsPos);
			globalsPos += align.typeSize(g);
		}

		globalTable = {
			sub : new Map(),
			gid : null,
		};
		function addGlobal( path : Array<String>, gid : Int ) {
			var t = globalTable;
			for( p in path ) {
				if( t.sub == null )
					t.sub = new Map();
				var next = t.sub.get(p);
				if( next == null ) {
					next = { sub : null, gid : null };
					t.sub.set(p, next);
				}
				t = next;
			}
			t.gid = gid;
		}
		typeCache = [];
		for( t in code.types )
			switch( t ) {
			case HObj(o), HStruct(o):
				typeCache.set(o.name, t);
				if( o.globalValue == null )
					continue;
				var path = o.name.split(".");
				addGlobal(path, o.globalValue);
				// Add abstract type's original name as alias
				var hasAlias = false;
				var apath = [path[0]];
				for( i in 1...path.length ) {
					var n0 = apath[apath.length-1];
					var n1 = path[i];
					if( n0.charCodeAt(0) == "_".code && StringTools.endsWith(n1, "_Impl_") ) {
						hasAlias = true;
						n1 = n1.substring(0, n1.length - 6);
						apath.pop();
					}
					apath.push(n1);
				}
				if( hasAlias ) addGlobal(apath, o.globalValue);
			case HEnum(e):
				if( e.name != null )
					typeCache.set(e.name, t);
				if( e.globalValue == null )
					continue;
				addGlobal(e.name.split("."), e.globalValue);
			default:
			}
	}

	public function getObjectProto( o : ObjPrototype, isStruct : Bool ) : ModuleProto {

		var p = protoCache.get(o.name);
		if( p != null )
			return p;

		var parent = o.tsuper == null ? null : switch( o.tsuper ) { case HObj(o), HStruct(o): getObjectProto(o,isStruct); default: throw "assert"; };
		var size = parent == null ? (isStruct ? 0 : align.ptr) : parent.size - parent.padSize;
		var largestField = parent == null ? size : parent.largestField;
		var fields = parent == null ? new Map() : [for( k in parent.fields.keys() ) k => parent.fields.get(k)];
		var mindex = 0;
		var methods = parent == null ? new Map() : [for( k => v in parent.methods ) k => {
			mindex++;
			v;
		}];

		for( f in o.fields ) {
			var pad = f.t;
			switch( pad ) {
			case HPacked(t):
				// align on packed largest field
				switch( t.v ) {
				case HStruct(o):
					var large = getObjectProto(o,true).largestField;
					var pad = size % large;
					if( pad != 0 )
						size += large - pad;
					if( large > largestField )
						largestField = large;
				default: throw "assert";
				}
			default:
				size += align.padStruct(size, pad);
			}
			fields.set(f.name, { name : f.name, t : f.t, offset : size });
			size += switch( f.t ) {
			case HPacked({ v : HStruct(o) }): getObjectProto(o,true).size;
			case HPacked(_): throw "assert";
			default:
				var sz = align.typeSize(f.t);
				if( sz > largestField ) largestField = sz;
				sz;
			}
		}

		var padSize = 0;
		if( largestField > 0 ) {
			var pad = size % largestField;
			if( pad != 0 ) {
				padSize = largestField - pad;
				size += padSize;
			}
		}

		for( m in o.proto ) {
			var idx = functionsIndexes.get(m.findex);
			var f = code.functions[idx];
			// parent methods are placed before child
			if( parent != null && m.pindex >= 0 ) {
				var v = parent.methods.get(m.name);
				if( v != null )
					methods.set(m.name, { t : f.t, index : v.index, pindex : m.pindex });
				else
					methods.set(m.name, { t : f.t, index : mindex++, pindex : m.pindex });
			} else {
				methods.set(m.name, { t : f.t, index : mindex++, pindex : m.pindex });
			}
		}

		p = {
			name : o.name,
			size : size,
			padSize : padSize,
			largestField: largestField,
			parent : parent,
			fields : fields,
			methods : methods,
			fieldNames : [for( o in o.fields ) o.name],
		};
		protoCache.set(p.name, p);

		return p;
	}

	public function getEnumProto( e : EnumPrototype ) : ModuleEProto {
		if( e.name == null )
			e.name = "$Closure:"+closureContextId++;
		var p = eprotoCache.get(e.name);
		if( p != null )
			return p;
		p = [];
		for( c in e.constructs ) {
			var size = align.ptr;
			size += align.padStruct(size, HI32);
			size += 4; // index
			var params = [];
			for( t in c.params ) {
				size += align.padStruct(size, t);
				params.push({ offset : size, t : t });
				size += align.typeSize(t);
			}
			p.push({ name : c.name, size : size, params : params });
		}
		eprotoCache.set(e.name, p);
		return p;
	}

	public function resolveGlobal( path : Array<String> ) {
		var g = globalTable;
		while( path.length > 0 ) {
			if( g.sub == null ) break;
			var p = path[0];
			var n = g.sub.get(p);
			if( n == null ) break;
			path.shift();
			g = n;
		}
		return g == globalTable || g.gid == null ? null : { type : code.globals[g.gid], offset : globalsOffsets[g.gid] };
	}

	public function resolveType( path : String ) {
		return typeCache.get(path);
	}

	public function resolveEnum( path : String ) {
		var et = typeCache.get(path);
		return switch( et ) {
		case HEnum(e): e;
		default: null;
		}
	}

	public function getFileFunctions( file : String ) {
		var ifile = fileIndexes.get(file);
		if( ifile == null )
			ifile = fileIndexes.get(file.split("\\").join("/").toLowerCase());
		if( ifile == null )
			return null;
		var functions = functionsByFile.get(ifile);
		if( functions == null )
			return null;
		return { functions : functions, fidx : ifile };
	}

	public function getBreaks( file : String, line : Int ) {
		var ffuns = getFileFunctions(file);
		if( ffuns == null )
			return null;

		var breaks = [];
		var funs = ffuns.functions;
		var matched = [];

		while( breaks.length == 0 && funs.length > 0 ) {
			for( f in funs ) {
				if( f.lmin > line || f.lmax < line ) continue;
				matched.push(f);
				var ifun = f.ifun;
				var f = f.f;
				var i = 0;
				var len = f.debug.length >> 1;
				var first = -1;
				/**
					Because of inlining or switch compilation we might have several instances
					of the same code duplicated within the same method, let's match continous
					groups
				**/
				while( i < len ) {
					var dfile = f.debug[i << 1];
					if( dfile != ffuns.fidx ) {
						i++;
						continue;
					}
					var dline = f.debug[(i << 1) + 1];
					if( dline != line ) {
						i++;
						continue;
					}
					var op = f.ops[i].getIndex();
					if( first == -1 || first == op ) {
						first = op;
						breaks.push({ ifun : ifun, pos : i });
					}
					// skip
					i++;
					while( i < len ) {
						var dfile = f.debug[i << 1];
						var dline = f.debug[(i << 1) + 1];
						if( dfile == ffuns.fidx && dline != line )
							break;
						i++;
					}
				}
			}
			// breakpoint not found ? move to the next line
			if( breaks.length == 0 ) {
				funs = matched;
				matched = [];
				line++;
			}
		}
		return { breaks : breaks, line : line };
	}

	public function isValid( fidx : Int, fpos : Int ) {
		var f = code.functions[fidx];
		var fid = f.debug[fpos << 1];
		return code.debugFiles[fid] != "?";
	}

	public function resolveSymbol( fidx : Int, fpos : Int ) {
		var f = code.functions[fidx];
		var fid = f.debug[fpos << 1];
		var fline = f.debug[(fpos << 1) + 1];
		var spans = opcodeSourceSpans.get(fidx), span = spans == null ? null : spans.get(fpos);
		return span == null ? { file : code.debugFiles[fid], line : fline, start : -1, end : -1, flags : 0 }
			: { file : span.sourcePath, line : span.line, start : span.start, end : span.end, flags : span.flags };
	}

	public function getFunctionRegs( fidx : Int ) {
		var regs = functionRegsCache[fidx];
		if( regs != null )
			return regs;
		var f = code.functions[fidx];
		var nargs = switch( f.t ) { case HFun(f): f.args.length; default: throw "assert"; };
		regs = [];

		var argsSize = 0;
		var size = 0;
		var floatRegs = 0, intRegs = 0;
		for( i in 0...nargs ) {
			var t = f.regs[i];
			if( align.is64 && !isWindows ) {
				var isFloat = t.match(HF32 | HF64);
				if( (isFloat ? ++floatRegs : ++intRegs) <= 6 ) {
					// stored in locals
					size += align.typeSize(t);
					size += align.padSize(size, t);
					regs[i] = { t : t, offset : -size };
					continue;
				}
			}
			regs[i] = { t : t, offset : argsSize + align.ptr * 2 };
			argsSize += align.stackSize(t);
		}
		for( i in nargs...f.regs.length ) {
			var t = f.regs[i];
			size += align.typeSize(t);
			size += align.padSize(size, t);
			regs[i] = { t : t, offset : -size };
		}
		functionRegsCache[fidx] = regs;
		return regs;
	}

	public function reverseHash( h : Int ) {
		if( reversedHashes == null ) {
			reversedHashes = new Map();
			for( s in code.strings )
				reversedHashes.set(s.hash(), s);
		}
		return reversedHashes.get(h);
	}

	public function getGraph( fidx : Int ) {
		var g = graphCache.get(fidx);
		if( g != null )
			return g;
		g = new CodeGraph(code, code.functions[fidx]);
		graphCache.set(fidx, g);
		return g;
	}

}
