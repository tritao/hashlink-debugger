package hld;

enum StepMode {
	Out;
	Next;
	Into;
}

enum DebugRegsKind {
	HLRegs;
	Regs;
	NatRegs;
}

@:publicFields @:structInit
class Address {
	var ptr : Pointer;
	var t : format.hl.Data.HLType;
}

@:publicFields @:structInit
class WatchPoint {
	var addr : Address;
	var regs : Array<{ offset : Int, bits : Int, r : Api.Register }>;
	var forReadWrite : Bool;
}

@:publicFields @:structInit
class StackRawInfo {
	var fidx : Int;
	var fpos : Int;
	var codePos : Pointer;
	var ebp : Null<hld.Pointer>;
	@:optional var jit : JitInfo;
	@:optional var module : Module;
}

@:publicFields @:structInit
class BreakContext {
	var rip : Pointer;
	var regs : Array<Pointer>;
}

@:publicFields @:structInit
class StackInfo {
	var file : String;
	var line : Int;
	@:optional var column : Int;
	@:optional var endLine : Int;
	@:optional var endColumn : Int;
	@:optional var sourceHash : Int;
	@:optional var start : Int;
	@:optional var end : Int;
	var ebp : Pointer;
	var context : Null<{ obj : format.hl.Data.ObjPrototype, field : String }>;
	@:optional var functionName : String;
}

class Debugger {

	public static inline var NATIVE_FRAME = "<native>";
	static inline var INT3 = 0xCC;
	static var HW_REGS : Array<Api.Register> = [Dr0, Dr1, Dr2, Dr3];
	public static var DEBUG = false;
	public static var IGNORED_ROOTS = [
		"hl",
		"sys",
		"haxe",
		"Date",
		"EReg",
		"Math",
		"Reflect",
		"Std",
		"String",
		"StringBuf",
		"Sys",
		"Type",
		"Xml",
		"IntIterator",
		"ArrayObj" // special
	];

	var sock : #if hxnodejs js.node.net.Socket #else sys.net.Socket #end;

	var api : Api;
	var module : Module;
	var jit : JitInfo;
	var processExit : Bool;
	var debugProtocolStarted = false;
	var mappingRequestPending = false;
	var revisionNotificationPending = false;
	var pendingRebinds : Array<{ fid : Int, pos : Int, codePos : Pointer, oldByte : Int, condition : String, ?jit : JitInfo, ?module : Module, ?stableId : Int }>;
	var ignoredRoots : Map<String,Bool>;

	var breakPoints : Array<{ fid : Int, pos : Int, codePos : Pointer, oldByte : Int, condition : String, ?jit : JitInfo, ?module : Module, ?stableId : Int, ?functionBreakpoint : Bool }>;
	var nextStep(default,set): Pointer = Pointer.make(0,0);
	var currentStack : Array<StackRawInfo>;
	var watches : Array<WatchPoint>;
	var threads : Map<Int,{ id : Int, stackTop : Pointer, exception : Pointer, ?exceptionStack: Array<StackRawInfo>, ?exceptionTrap: Pointer, ?breakContext: BreakContext, name : String }>;
	var afterStep = false;

	public var is64(get, never) : Bool;

	public var eval : Eval;
	var evalByModule : haxe.ds.ObjectMap<Module,Eval>;
	public var currentStackFrame : Int;
	public var breakOnThrow(default, set) : Bool;
	public var stackFrameCount(get, never) : Int;
	public var mainThread(default, null) : Int = 0;
	public var stoppedThread(default,set) : Null<Int>;
	public var currentThread(default,set) : Null<Int>;

	public var customTimeout : Null<Float>;
	public var onDebugMappingsChanged : Void -> Void;

	public var watchBreak : Address; // set if breakpoint occur on watch expression

	public function new() {
		breakPoints = [];
		watches = [];
	}

	function set_nextStep(v:Pointer) {
		if( DEBUG ) trace("NEXT STEP "+jit.codePtrToString(v));
		return nextStep = v;
	}

	function set_currentThread(v) {
		currentThread = v;
		eval.currentThread = v;
		return v;
	}

	function set_stoppedThread(v) {
		return stoppedThread = currentThread = v;
	}

	function get_is64() {
		return jit.is64;
	}

	public function loadModule( content : haxe.io.Bytes ) {
		module = new Module();
		module.load(content);
	}

	public function connectTries( host : String, port : Int, timeout : Float, onResult : Bool -> Void, ?retry : Void -> Bool ) {
		if( timeout <= 0 ) {
			onResult(false);
			return;
		}
		var ts = Sys.time();
		connect(host,port,function(b) {
			if( b ) {
				onResult(true);
				return;
			}
			if( retry != null && !retry() ) {
				onResult(false);
				return;
			}
			haxe.Timer.delay(function() {
				connectTries(host, port, timeout - (Sys.time()-ts), onResult, retry);
			},20);
		});
	}

	public function connect( host : String, port : Int, onResult : Bool -> Void ) {
		var initialResultPending = false;
		function done(input:haxe.io.BytesInput) {
			jit = new JitInfo();
			if( !jit.read(input, module) ) {
				close();
				onResult(false);
				return;
			}
			module.init(jit.align);
			if( jit.protocolVersion == 3 ) {
				DebugTrace.write("debugger", "hld3_connected", { modules : 1 + jit.debugModules.length });
				debugProtocolStarted = true;
				initialResultPending = true;
				#if hxnodejs sock.write("A") #else sock.output.writeByte("A".code) #end;
			} else
				onResult(true);
		}

		#if hxnodejs
		var inputData = haxe.io.Bytes.alloc(0);
		var connected = false;
		function appendData(buf:js.node.Buffer) {
			var chunk = haxe.io.Bytes.ofData(buf.buffer).sub(buf.byteOffset, buf.byteLength);
			var merged = haxe.io.Bytes.alloc(inputData.length + chunk.length);
			merged.blit(0, inputData, 0, inputData.length);
			merged.blit(inputData.length, chunk, 0, chunk.length);
			inputData = merged;
		}
		function consume() {
			var input = new haxe.io.BytesInput(inputData);
			try {
				if( !connected ) {
					done(input);
					connected = true;
				} else {
					var marker = input.readString(4);
					if( marker == "REV3" ) {
						var identityLow = input.readInt32();
						var identityHigh = jit.is64 ? input.readInt32() : 0;
						var revision = input.readInt32();
						if( revision <= 0 ) throw "Invalid REV3 revision";
						DebugTrace.write("debugger", "rev3_received", { moduleLow : identityLow, moduleHigh : identityHigh, revision : revision });
						revisionNotificationPending = true;
						requestDebugMappings();
					} else if( marker == "MAP3" ) {
						if( !jit.readRefresh(input, false) ) { close(); return; }
						DebugTrace.write("debugger", "map3_applied", { modules : 1 + jit.debugModules.length, breakpoints : breakPoints.length });
						mappingRequestPending = false;
						if( revisionNotificationPending ) applyRevisionMappings() else rebindBreakpoints();
						if( onDebugMappingsChanged != null ) onDebugMappingsChanged();
						if( initialResultPending ) { initialResultPending = false; onResult(true); }
					} else if( marker == "ACK3" ) {
						DebugTrace.write("debugger", "ack3_received");
						if( !initialResultPending ) throw "Unexpected ACK3";
						initialResultPending = false;
						onResult(true);
					} else if( marker == "BRK3" ) {
						var count = input.readInt32();
						if( pendingRebinds == null || count != pendingRebinds.length ) throw "Invalid BRK3 response";
						for( index in 0...count ) pendingRebinds[index].oldByte = input.readByte();
						DebugTrace.write("debugger", "brk3_received", { count : count });
						pendingRebinds = null;
						finishRevisionMappings();
					} else {
						close();
						return;
					}
				}
				inputData = inputData.sub(input.position, inputData.length - input.position);
				if( inputData.length > 0 ) consume();
			} catch( e : haxe.io.Eof ) {
				// Keep the complete frame until another socket chunk arrives.
			}
		}
		sock = new js.node.net.Socket();
		sock.on("data", function(buf:js.node.Buffer) {
			appendData(buf);
			consume();
		});
		js.node.Dns.lookup(host, {family: 4}, function(err, address:String, family) {
			if( err != null ) {
				onResult(false);
				return;
			}
			sock.on("error", function(err) {
				if( onResult != null ) {
					close();
					onResult(false);
					return;
				}
			});
			sock.connect(port, address, function() {
				// wait data
			});
		});
		#else
		sock = new sys.net.Socket();
		try {
			sock.connect(new sys.net.Host(host), port);
		} catch( e : Dynamic ) {
			sock.close();
			Sys.sleep(0.1);
			onResult(false);
			return;
		}
		done(sock.input);
		#end
	}

	public function init( api : Api ) {
		this.api = api;
		evalByModule = new haxe.ds.ObjectMap();
		eval = makeEval(module, jit);
		if( !api.start() )
			return false;
		wait(); // wait first break
		return true;
	}

	function makeEval(ownerModule:Module, ownerJit:JitInfo) {
		var out = new Eval(ownerModule, api, ownerJit);
		out.resumeDebug = evalResumeDebug;
		out.setSingleStep = singleStep;
		evalByModule.set(ownerModule, out);
		return out;
	}

	function evalResumeDebug() {
		resume();
		wait(false, true);
	}

	function close() {
		DebugTrace.write("debugger", "socket_close");
		if( sock != null ) {
			#if hxnodejs sock.destroy() #else sock.close() #end;
			sock = null;
		}
	}

	public function run() {
		DebugTrace.write("debugger", "run_enter", { stoppedThread : stoppedThread });
		afterStep = false;
		// closing the socket will unlock waiting thread
		if( jit.protocolVersion != 3 )
			close();
		else if( !debugProtocolStarted ) {
			debugProtocolStarted = true;
			// A starts an HLD3 target without taking a redundant live snapshot.
			// Later snapshots are revision-driven and publication-synchronized.
			#if hxnodejs sock.write("A") #else sock.output.writeByte("A".code) #end;
		}
		if( stoppedThread != null )
			resume();
		return wait();
	}

	public function requestDebugMappings() {
		if( jit == null || jit.protocolVersion != 3 || sock == null || mappingRequestPending ) return;
		mappingRequestPending = true;
		DebugTrace.write("debugger", "map3_requested");
		#if hxnodejs sock.write("R") #else sock.output.writeByte("R".code) #end;
	}

	function applyRevisionMappings() {
		pendingRebinds = [];
		for( bp in breakPoints ) {
			if( bp.fid < 0 ) continue;
			var owner = bp.jit == null ? jit : bp.jit;
			var current = owner.moduleIdentity == null ? owner : findJitModule(owner.moduleIdentity);
			if( current == null ) continue;
			var rebound = bp.stableId == null ? bp.fid : current.findFunctionByStableId(bp.stableId);
			if( rebound == null || !current.hasFunction(rebound) ) continue;
			bp.fid = rebound;
			var next = current.getCodePos(bp.fid, bp.pos);
			if( next == bp.codePos ) continue;
			bp.jit = current;
			bp.module = current.module;
			bp.codePos = next;
			pendingRebinds.push(bp);
		}
		if( pendingRebinds.length == 0 ) { pendingRebinds = null; finishRevisionMappings(); return; }
		DebugTrace.write("debugger", "breakpoints_rebind_requested", { count : pendingRebinds.length });
		var output = new haxe.io.BytesOutput();
		output.bigEndian = false;
		output.writeByte("B".code);
		output.writeInt32(pendingRebinds.length);
		for( bp in pendingRebinds ) {
			output.writeInt32(bp.codePos.i64.low);
			if( jit.is64 ) output.writeInt32(bp.codePos.i64.high);
			output.writeByte(INT3);
		}
		var bytes = output.getBytes();
		#if hxnodejs sock.write(js.node.Buffer.from(bytes.getData())) #else sock.output.write(bytes) #end;
	}

	function finishRevisionMappings() {
		revisionNotificationPending = false;
		DebugTrace.write("debugger", "revision_acknowledged");
		#if hxnodejs sock.write("A") #else sock.output.writeByte("A".code) #end;
	}

	function rebindBreakpoints() {
		for( bp in breakPoints ) {
			if( bp.fid < 0 ) continue;
			var owner = bp.jit == null ? jit : bp.jit;
			var current = owner.moduleIdentity == null ? owner : findJitModule(owner.moduleIdentity);
			if( current == null ) continue;
			var rebound = bp.stableId == null ? bp.fid : current.findFunctionByStableId(bp.stableId);
			if( rebound == null || current.getFunctionVars(rebound) == null ) continue;
			bp.fid = rebound;
			var next = current.getCodePos(bp.fid, bp.pos);
			if( next == bp.codePos ) continue;
			// Old regions may already have been retired; only install the new trap.
			bp.jit = current;
			bp.module = current.module;
			bp.codePos = next;
			bp.oldByte = getAsm(next);
			setAsm(next, INT3);
		}
	}

	function findJitModule(identity:Pointer):JitInfo {
		if( jit.moduleIdentity == identity ) return jit;
		for( item in jit.debugModules ) if( item.moduleIdentity == identity ) return item;
		return null;
	}

	public function getThreads() {
		var tl = [for( t in threads ) t.id];
		tl.sort(Reflect.compare);
		return tl;
	}

	public function setCurrentThread(tid) {
		currentThread = tid;
		prepareStack();
	}

	public function pause() {
		if( !api.breakpoint() )
			throw "Failed to break process";
		var r = wait(false, false, true);
		// if we have stopped on a not HL thread, let's switch on main thread
		var found = false;
		for( t in threads )
			if( t.id == stoppedThread ) {
				found = true;
				break;
			}
		if( !found ) {
			currentThread = mainThread;
			prepareStack();
		}
		return r;
	}

	function singleStep(tid,set=true) {
		var r = getReg(tid, EFlags).toInt();
		if( set ) r |= 256 else r &= ~256;
		if( DEBUG ) trace("SINGLESTEP "+set);
		setReg(tid, EFlags, hld.Pointer.make(r,0));
	}

	public var exceptionDecodeError(default, null) : Null<String>;

	public function hasException() : Bool {
		var t = threads.get(currentThread);
		return t != null && !t.exception.isNull();
	}

	public function getException() : Null<Value> {
		exceptionDecodeError = null;
		var t = threads.get(currentThread);
		if( t == null || t.exception.isNull() )
			return null;
		try {
			return decodeException(t.exception);
		} catch( e : Dynamic ) {
			exceptionDecodeError = Std.string(e);
			if( DEBUG ) trace("Failed to decode exception: " + exceptionDecodeError);
			return null;
		}
	}

	function decodeException( exc : Pointer ) : Value {
		var v = eval.readVal(exc, HDyn);
		switch( v.t ) {
		case HObj({ name : "haxe.ValueException" }):
			try v = eval.readField(v, "value") catch( e : Dynamic ) {}
		case HObj({ name : "SysError" }):
			try {
				switch( eval.readField(v, "msg").v ) {
				case VString(msg, p):
					v = { v : VString("SysError: " + msg, p), t : v.t };
				default:
				}
			} catch( e : Dynamic ) {}
		default:
		}
		switch( v.v ) {
		case VBytes(_, _, p) if( v.t.match(HBytes) ):
			var str = try eval.readUCSBytes(p) catch( e : Dynamic ) "";
			v = { v : VString(str, p), t : v.t };
		default:
		}
		return v;
	}

	public function getVMExceptionStack() {
		var t = threads.get(currentThread);
		if( t == null )
			return null;
		var stack = t.exceptionStack;
		if( stack == null )
			return null;
		return stack.map(e -> stackInfo(e));
	}

	public function hasStack() {
		return currentStack.length > 0;
	}

	public function getCurrentVars( args : Bool ) {
		var s = currentStack[currentStackFrame];
		if( s == null || s.fidx == Eval.TRAMPOLINE_FIDX ) return [];
		var owner = s.module == null ? module : s.module;
		var g = owner.getGraph(s.fidx);
		if( args )
			return g.getArgs();
		var locals = g.getLocals(s.fpos);
		if( afterStep && currentStackFrame == 0 && g.getReturnReg(s.fpos) != null )
			locals.push("$ret");
		return locals;
	}

	public function getDebugContext() : String {
		if( !setContext(false) )
			return null;
		return eval.getContextStr();
	}

	public function getDebugRegs( kind : DebugRegsKind, ?fidx : Int ) : Array<String> {
		if( kind == NatRegs && fidx != null )
			return eval.getNatRegs(fidx);
		if( !setContext(false) )
			return [];
		return switch( kind ) {
		case HLRegs: eval.getHLRegs();
		case Regs: eval.getDebugRegs();
		case NatRegs: eval.getNatRegs(fidx);
		}
	}

	public function getOpPositions( fidx : Int, from : Int, to : Int ) : Array<String> {
		var out = [];
		var start = jit.getFunctionPos(fidx);
		var f = module.code.functions[fidx];
		if( to > f.ops.length ) to = f.ops.length;
		for( i in from...to ) {
			var s = module.resolveSymbol(fidx, i);
			out.push('@$i [${s.line}] +0x${StringTools.hex(jit.getCodePos(fidx,i).sub(start))} ${f.ops[i]}');
		}
		return out;
	}

	public function getCurrentClass() {
		var s = currentStack[currentStackFrame];
		if( s.fidx == Eval.TRAMPOLINE_FIDX )
			return null;
		var owner = s.module == null ? module : s.module;
		var ctx = owner.getMethodContext(s.fidx);
		if( ctx == null )
			return null;
		var name = ctx.obj.name;
		return name.split("$").join("");
	}

	public function getClassStatics( cl : String ) {
		var v = getValue(cl, true);
		if( v == null )
			throw "No such class "+cl;
		var fields = eval.getFields(v);
		fields.remove("__name__");
		fields.remove("__type__");
		fields.remove("__meta__");
		fields.remove("__implementedBy__");
		fields.remove("__constructor__");
		return fields;
	}

	function wait( onSingleStep = false, onEvalCall = false, onPause = false ) : Api.WaitResult {
		var cmd = null;
		var condition : String = null;
		watchBreak = null;
		while( true ) {
			cmd = api.wait(customTimeout == null ? 1000 : Math.ceil(customTimeout * 1000));
			if( cmd.r != Timeout && cmd.r != Handled ) DebugTrace.write("debugger", "native_wait", { result : Std.string(cmd.r), thread : cmd.tid });

			if( cmd.r == Breakpoint && !onEvalCall && (jit.isCodePtr(nextStep) || onSingleStep) ) {
				// On Linux, singlestep is not reset
				cmd.r = SingleStep;
				singleStep(cmd.tid,false);
			}

			if( DEBUG ) switch(cmd.r) {
				case Error:
					trace("**** ERROR ****");
				case Breakpoint:
					trace("BREAK");
				case SingleStep:
					trace("STEP");
				case Exit:
					trace("EXIT");
				case Handled, Timeout:
				default:
					trace(cmd.r);
				}

			var tid = cmd.tid;
			switch( cmd.r ) {
			case Timeout, Handled:

				if( customTimeout != null )
					return cmd.r;

			case Breakpoint:
				var codePos = getCodePos(tid).offset(-1);
				DebugTrace.write("debugger", "trap_received", { thread : tid, address : codePos.toString(), known : Lambda.exists(breakPoints, function(b) return b.codePos == codePos) });
				for( b in breakPoints ) {
					if( b.codePos == codePos ) {
						condition = b.condition;
						// restore code
						setAsm(codePos, b.oldByte);
						// move backward
						setReg(tid, Eip, getReg(tid, Eip).offset(-1));
						singleStep(tid);
						nextStep = codePos;
						break;
					}
				}
				break;
			case SingleStep:
				// restore our breakpoint
				if( jit.isCodePtr(nextStep) ) {
					setAsm(nextStep, INT3);
					nextStep = Pointer.make(0, 0);
				} else if( watches.length > 0 ) {

					// check if we have a break on a watchpoint
					var dr6 = api.readRegister(tid, Dr6);
					var watchBits = dr6.toInt() & 15;
					if( watchBits != 0 ) {
						for( w in watches )
							for( r in w.regs )
								if( watchBits & (1 << HW_REGS.indexOf(r.r)) != 0 ) {
									watchBreak = w.addr;
									break;
								}
						api.writeRegister(tid, Dr6, Pointer.make(0, 0));
						if( watchBreak != null ) {
							cmd.r = Watchbreak;
							break;
						}
					}

				}
				stoppedThread = tid;
				if( onSingleStep )
					return SingleStep;
				resume();
			case Exit:
				processExit = true;
				break;
			case Error, Watchbreak, StackOverflow:
				break;
			}
		}
		stoppedThread = cmd.tid;

		// Do not overwrite stack on evalCall
		if( onEvalCall )
			return cmd.r;

		// in thread-disabled we don't know the main thread id in HL:
		// first stop is on a special thread in windows
		// wait for second stop with is user-specific
		if( jit.oldThreadInfos != null )
			mainThread = jit.oldThreadInfos.id;
		else if( mainThread == 0 )
			mainThread = -1;
		else if( mainThread == -1 )
			mainThread = stoppedThread;

		readThreads();
		prepareStack(cmd.r == Watchbreak);
		eval.onBeforeBreak();

		// if breakpoint has a condition, try to evaluate and do not actually break on false
		if( !onSingleStep && !onEvalCall && !onPause && condition != null ) {
			try {
				var value = getValue(condition);
				if( value != null ) {
					switch( value.v ) {
					case VBool( b ) if( !b ): return Handled;
					default:
					}
				}
			} catch( e : Dynamic ) {
				trace("Can't evaluate condition (" + condition + ") for breakpoint: " + e);
			}
		}
		return cmd.r;
	}

	public function getThreadName( id : Int, ?opt ) {
		var t = threads.get(id);
		return t == null || t.name == null ? (opt == null ? "Thread "+id : opt) : t.name+":"+id;
	}

	function readThreads() {
		var old = jit.oldThreadInfos;
		threads = new Map();
		if( old != null ) {
			threads.set(old.id, { id : old.id, stackTop : old.stackTop, exception : eval.readPointer(old.debugExc), name : "Main" });
			return;
		}
		var count = eval.readI32(jit.threads);
		var tinfos = eval.readPointer(jit.threads.offset(8));
		var flagsPos = jit.align.ptr * 6 + 8;
		var excPos = jit.align.ptr * 5 + 8;
		var excTrapPos = jit.align.ptr * 2 + 8;
		var excStackCountPos = flagsPos + 4;
		var excStackPos = flagsPos + 8 + 256 + (jit.hlVersion >= 1.13 ? 128 : 0);
		var namePos = jit.hlVersion >= 1.13 ? flagsPos + 8 : -1;
		var breakPos = excStackPos + 256 * jit.align.ptr;
		for( i in 0...count ) {
			var tinf = eval.readPointer(tinfos.offset(jit.align.ptr * i));
			var tid = eval.readI32(tinf);
			var flags = eval.readI32(tinf.offset(flagsPos));
			if( flags & 16 != 0 ) continue; // invisible
			if( tid == 0 )
				tid = mainThread;
			else if( mainThread <= 0 )
				mainThread = tid;
			var name = null;
			if( namePos >= 0 ) {
				var tname = @:privateAccess eval.readMem(tinf.offset(namePos), 128).readStringUTF8();
				if( tname != "" )
					name = tname;
			}
			var trapCtx = eval.readPointer(tinf.offset(excTrapPos));
			var t = {
				id : tid,
				stackTop : eval.readPointer(tinf.offset(8)),
				exception : flags & 4 == 0 ? null : tinf.offset(excPos),
				exceptionStack : flags & 1 == 0 ? null : readVMExceptionStack(tinf.offset(excStackPos), eval.readI32(tinf.offset(excStackCountPos))),
				exceptionTrap : trapCtx.isNull() ? null : new Pointer(eval.readPointer(trapCtx.offset(10 * 8))),
				breakContext : readBreakContext(tinf.offset(breakPos)),
				name : name,
			};
			threads.set(tid, t);
		}
		if( !threads.exists(currentThread) )
			threads.set(currentThread,{ id : currentThread, stackTop: null, exception: null, name : null });
	}

	function readBreakContext( base : Pointer ) : Null<BreakContext> {
		if( jit.hlVersion < 2 )
			return null;
		var rip = eval.readPointer(base);
		if( rip.isNull() || !jit.isCodePtr(rip) )
			return null;
		return {
			rip : rip,
			regs : [for( i in 0...32 ) eval.readPointer(base.offset((i + 1) * jit.align.ptr))],
		};
	}

	function readVMExceptionStack(base : Pointer, count : Int) : Array<StackRawInfo> {
		var stack = [];
		if( count <= 0 || count >= 256 || base.isNull() )
			return stack;
		for( i in 0...count ) {
			var codePtr = eval.readPointer(base.offset(i * jit.align.ptr));
			var e = jit.resolveAsmPos(codePtr);
			if( e != null )
				stack.push(e);
		}
		return [for( s in stack ) if( isValidRaw(s) ) s];
	}

	function prepareStack( isWatchbreak=false ) {
		currentStackFrame = 0;
		currentStack = makeStack(currentThread, isWatchbreak);
		var t = threads.get(currentThread);
		var brk = t == null ? null : t.breakContext;
		eval.breakRegs = brk == null ? null : brk.regs;
		eval.nativeBreak = brk == null && stoppedThread != null && jit.resolveAsmPos(getCodePos(currentThread)) == null;
	}

	function skipFunction( fidx : Int, ?owner : Module ) {
		if( owner == null ) owner = module;
		var ctx = owner.getMethodContext(fidx);
		var name = ctx == null ? new haxe.io.Path(owner.resolveSymbol(fidx, 0).file).file : ctx.obj.name.split(".")[0];
		if( name.charCodeAt(0) == "$".code ) name = name.substr(1);
		if( ignoredRoots == null ) {
			ignoredRoots = new Map();
			for( r in IGNORED_ROOTS )
				ignoredRoots.set(r,true);
		}
		return ignoredRoots.exists(name);
	}

	public function getStepInTargets(frame:Int = 0) {
		if( frame != 0 ) return [];
		var s = currentStack[frame];
		if( s == null || s.fidx == Eval.TRAMPOLINE_FIDX ) return [];
		var owner = s.module == null ? module : s.module;
		var graph = owner.getGraph(s.fidx), origin = owner.resolveSymbol(s.fidx, s.fpos);
		var todo = [s.fpos], seen = new Map<Int,Bool>(), targets = [];
		while( todo.length > 0 ) {
			var pos = todo.pop();
			if( seen.exists(pos) ) continue;
			seen.set(pos, true);
			var symbol = owner.resolveSymbol(s.fidx, pos);
			if( pos != s.fpos && ((symbol.flags & 1) != 0 || symbol.file != origin.file || symbol.line != origin.line) ) continue;
			switch( graph.control(pos) ) {
			case CCall(findex):
				var label = "dynamic call";
				if( findex >= 0 ) {
					var target = @:privateAccess owner.functionsIndexes.get(findex);
					if( target == null || target >= owner.code.functions.length || skipFunction(target, owner) ) {
						for( next in graph.getNextPos(pos) ) todo.push(next);
						continue;
					}
					label = owner.getFunctionDisplayName(target);
				}
				targets.push({pos:pos, label:label + " at " + symbol.line + ":" + symbol.column});
			default:
			}
			for( next in graph.getNextPos(pos) ) todo.push(next);
		}
		targets.sort(function(a, b) return a.pos - b.pos);
		return targets;
	}

	public function stepIntoTarget(pos:Int):Api.WaitResult {
		for( target in getStepInTargets() ) if( target.pos == pos ) return step(Into, pos);
		return step(Next);
	}

	public function step( mode : StepMode, ?targetPos:Int ) : Api.WaitResult {
		var tid = currentThread;
		var s = currentStack[0];
		var depth = currentStack.length;
		var onException = hasException();

		if( s == null || s.fidx == Eval.TRAMPOLINE_FIDX || onException ) {
			if( DEBUG ) trace("Step not supported, continue.");
			resume();
			return wait();
		}

		var orig = module.resolveSymbol(s.fidx, s.fpos);
		var graph = module.getGraph(s.fidx);
		var marked = new Map();
		var currentCodePos = getCodePos(tid);
		var onBreakPoint = false;
		var immediateProcess = false;

		for( b in breakPoints )
			if( b.fid == s.fidx ) {
				if( b.pos == s.fpos ) {
					onBreakPoint = true;
				} else
					marked.set(b.pos, null);
			}

		// Add trap breakpoint if current trap is not in current function
		var trap = threads.get(tid).exceptionTrap;
		if( trap != null ) {
			var e = jit.resolveAsmPos(trap);
			if( e != null && e.fidx != s.fidx ) {
				var old = getAsm(trap);
				var bp = { fid : -4, pos : e.fpos, codePos : trap, oldByte : old, condition : null };
				breakPoints.push(bp);
				marked.set(-1, bp);
				setAsm(trap, INT3);
			}
		}

		var todo = [s.fpos];
		while( todo.length > 0 ) {
			var pos = todo.pop();
			if( marked.exists(pos) )
				continue;
			var l = module.resolveSymbol(s.fidx, pos);
			var c = graph.control(pos);
			var hasSpans = orig.start >= 0 && l.start >= 0;
			var sourceChange = mode == Into && hasSpans ? l.file != orig.file || l.sourceHash != orig.sourceHash || l.start != orig.start || l.end != orig.end
				: l.file != orig.file || l.line != orig.line;
			var lineChange = targetPos == null && mode != Out && (l.flags & 1) == 0 && sourceChange && !c.match(CCatch | CJAlways(_));
			switch( c ) {
			case CCall(f) if( f >= 0 && mode == Into ):
				// skip calls to std library
				var fid = @:privateAccess module.functionsIndexes.get(f);
				if( fid == null || fid >= module.code.functions.length /* native */ || skipFunction(fid) )
					c = CNo;
			default:
			}
			if( targetPos != null && c.match(CCall(_)) && pos != targetPos ) c = CNo;
			if( lineChange || c == CRet || (mode == Into && c.match(CCall(_))) ) {
				var codePos = jit.getCodePos(s.fidx, pos);
				var old = getAsm(codePos);
				var bp = { fid : lineChange ? -1 : (c == CRet ? -2 : -3), pos : pos, codePos : codePos, oldByte : old, condition : null };
				breakPoints.push(bp);
				marked.set(pos, bp);
				if( codePos == currentCodePos && onBreakPoint ) {
					immediateProcess = true;
					bp.oldByte = -1;
				} else
					setAsm(codePos, INT3);
				// if we are on same op but after the call (after returning from a finish)
				if( c.match(CCall(_)) && codePos < currentCodePos )
					todo.push(pos+1);
				continue;
			}
			if( !c.match(CNo | CCall(_)) )
				marked.set(pos, null);
			for( p in graph.getNextPos(pos) )
				todo.push(p);
		}
		function cleanup() {
			for( bp in marked )
				if( bp != null ) {
					if( bp.oldByte == -1 )
						breakPoints.remove(bp);
					else
						removeBP(bp);
				}
		}
		if( !immediateProcess ) {
			while( true ) {
				resume();
				var r = wait();
				if( r != Exit && currentStack.length == 0 )
					r = wait();
				if( (r != Breakpoint && r != SingleStep) || currentThread != tid || currentStack.length == 0 || currentStack[0].fidx != s.fidx ) {
					cleanup();
					return r;
				}
				// fix recursive methods that are breaking on the inner function
				if( (mode == Out || mode == Next) && currentStack.length > depth ) {
					var isRecursive = false;
					for( b in breakPoints )
						if( (b.fid == -2 || b.fid == -1) && nextStep == b.codePos ) {
							isRecursive = true;
							break;
						}
					if( isRecursive ) {
						if( DEBUG ) trace("RECURSIVE");
						continue;
					}
				}
				break;
			}
		}
		// execute until the end of Call/Ret if we stopped on it !
		for( b in breakPoints ) {
			if( nextStep != b.codePos || b.fid >= -1 ) continue;
			var isRet = b.fid == -2;
			while( true ) {
				var eip = getReg(tid, Eip);
				var op = api.readByte(eip, 0);
				if( op == 0x48 )
					op = api.readByte(eip, 1);
				singleStep(tid);
				resume();
				var r = wait(true);
				if( r != SingleStep || currentThread != tid )
					break;
				var st = makeStack(tid,false,1)[0];
				if( isRet ) {
					if( op == 0xC3 ) {
						if( st == null ) {
							// ret on final main() ? - run till exit
							prepareStack();
							if( currentStack.length == 0 ) {
								resume();
								return wait();
							}
						}
						break;
					}
				} else {
					// call : wait we changed line !
					if( st != null && (st.fidx != s.fidx || st.fpos != b.pos) ) break;
				}
			}
			// in case we singleStepped !
			prepareStack();
			break;
		}
		cleanup();
		afterStep = true;
		return Breakpoint;
	}

	function isCallerOf( caller : StackRawInfo, callee : StackRawInfo ) {
		if( callee == null )
			return true;
		var f = module.code.functions[caller.fidx];
		if( f == null )
			return true;
		var graph = module.getGraph(caller.fidx);
		for( pos in [caller.fpos, caller.fpos - 1] ) {
			if( pos < 0 || pos >= f.ops.length )
				continue;
			switch( graph.control(pos) ) {
			case CCall(-1):
				return true;
			case CCall(findex):
				if( @:privateAccess module.functionsIndexes.get(findex) == callee.fidx )
					return true;
			default:
			}
		}
		return false;
	}

	function makeStack( tid, isWatchbreak : Bool, max = 0 ) {
		var stack = [];
		var tinf = threads.get(tid);
		if( tinf == null || tinf.stackTop == null )
			return stack;
		var brk = tinf.breakContext;
		var esp = brk == null ? getReg(tid, Esp) : brk.regs[(Eval.NativeReg.Esp : Eval.NativeReg).toInt()];
		var ebp = brk == null ? getReg(tid, Ebp) : brk.regs[(Eval.NativeReg.Ebp : Eval.NativeReg).toInt()];
		var size = tinf.stackTop.sub(esp) + jit.align.ptr;
		if( size < 0 ) size = 0;
		var memBase = esp.offset(-jit.align.ptr);
		var mem = tryReadMem(memBase, size);
		if( mem == null ) {
			var skip = findReadableBase(memBase, size);
			if( skip >= size )
				throw "Failed to read stack @" + memBase.toString() + "[" + size + "]";
			memBase = memBase.offset(skip);
			size -= skip;
			mem = readMem(memBase, size);
		}
		var prologPos = esp.sub(memBase) - jit.align.ptr;

		var eip = brk == null ? getReg(tid, Eip) : brk.rip;
		var asmPos = eip;
		if( isWatchbreak || brk != null )
			asmPos = asmPos.offset(-1);
		var e = jit.resolveAsmPos(asmPos);
		var inProlog = false;
		var exc = getException();
		var isExcCantCast = false;
		if( exc != null ) {
			switch( exc.v ){
			case VString(v,_):
				if( StringTools.startsWith(v, "Can't cast ") )
					isExcCantCast = true;
			default:
			}
		}

		//trace(eip,"0x"+api.readByte(eip, 0), e);

		if( e != null && !isValidRaw(e) )
			e = null;

		// if we are on ret, our EBP is wrong, so let's ignore this stack part
		if( e != null && brk == null ) {
			var op = api.readByte(eip, 0);
			if( op == 0x48 && jit.is64 )
				op = api.readByte(eip, 1);
			if( op == 0xC3 ) // RET
				e = null;
		}

		if( e != null ) {
			if( e.fpos < 0 && jit.is64) {
				// we can't consider being in a function while we are in the prolog
				// because our regs args have not yet been stored on stack
				e = null;
			} else if( e.fpos < 0 ) {
				// we are in function prolog
				var ownerJit = e.jit == null ? jit : e.jit;
				var delta = ownerJit.getFunctionPos(e.fidx).sub(asmPos);
				e.fpos = 0;
				if( delta == 0 )
					e.ebp = esp.offset(-jit.align.ptr); // not yet pushed ebp
				else
					e.ebp = esp;
				inProlog = true;
			} else
				e.ebp = ebp;
			if( e != null )
				stack.push(e);
		}

		// when requiring only top level stack, do not look further if we are in a C function
		// because we need to step so we don't want false positive
		if( max == 1 ) return stack;

		inline function readStack( p : Pointer ) : Null<Pointer> {
			var offset = p.sub(memBase);
			return offset < 0 || offset + jit.align.ptr > size ? null : mem.getPointer(offset, jit.align);
		}

		function fromNative( f : StackRawInfo ) {
			if( f.ebp == null )
				return true;
			var ret = readStack(f.ebp.offset(jit.align.ptr));
			if( ret == null )
				return true;
			var e = jit.resolveAsmPos(ret);
			return e == null || !isValidRaw(e);
		}

		// similar to module/module_capture_stack
		if( is64 ) {
			// on windows x64, we can't guarantee a stack pointer for our native funs...
			var skipFirstCheck = (e == null && jit.isWinCall);
			var trampoline = jit.trampoline;
			var atGap = e == null || fromNative(e);
			for( i in 0...(size >> 3)-1 ) {
				var val = mem.getPointer(i << 3, jit.align);
				if( atGap && trampoline != null && val == trampoline.marker ) {
					var slot = memBase.offset(i << 3);
					var frameEbp = readStack(slot.offset(trampoline.rbpOffset));
					var callSite = readStack(slot.offset(trampoline.callOffset));
					if( frameEbp != null && callSite != null && frameEbp > esp && frameEbp < tinf.stackTop ) {
						var e = jit.resolveAsmPos(callSite.offset(-1));
						if( e != null && e.fpos >= 0 && isValidRaw(e) ) {
							e.ebp = frameEbp;
							stack.push({ fidx : Eval.TRAMPOLINE_FIDX, fpos : 0, codePos : val, ebp : slot });
							stack.push(e);
							atGap = fromNative(e);
							skipFirstCheck = false;
							if( max > 0 && stack.length >= max ) return stack;
							continue;
						}
					}
				}
				if( (val > esp && val < tinf.stackTop) || (inProlog && (i << 3) == prologPos) || skipFirstCheck ) {
					var codePtr = skipFirstCheck ? val : mem.getPointer((i + 1) << 3, jit.align);
					var e = jit.resolveAsmPos(codePtr);
					if( e != null && e.fpos >= 0 && isCallerOf(e, stack[stack.length - 1]) ) {
						if( skipFirstCheck ) {
							e.ebp = ebp;
							// this ebp might not be good, so let's look for
							// the first potential ebp backup starting after our esi
							var validEsp = esp.offset(i << 3);
							if( e.ebp < validEsp || e.ebp > tinf.stackTop ) {
								var k = i - 1;
								if( isExcCantCast && is64 && jit.isWinCall ) {
									// Only do this for can't cast, as Null access .xxx has RSP+10h valid but is wrong
									// look first at saved RBP at prev RSP+10h
									var val2 = mem.getPointer((i + 2) << 3, jit.align); // Can't cast xxx to i32
									var val4 = mem.getPointer((i + 4) << 3, jit.align); // Can't cast xxx to obj (e.g String)
									var val = null;
									if( val2 > validEsp && val2 < tinf.stackTop ) val = val2;
									if( val4 > validEsp && val4 < tinf.stackTop ) val = val4;
									if( val != null ) {
										e.ebp = val;
										k = -1;
									}
								}
								var first = true;
								while( k > 0 ) {
									var val = mem.getPointer((k--) << 3, jit.align);
									if( val > validEsp && val < tinf.stackTop ) {
										var code = readMem(val.offset(jit.align.ptr),jit.align.ptr).getPointer(0, jit.align);
										if( !jit.isCodePtr(code) ) continue;
										if( first || val < e.ebp ) {
											e.ebp = val;
											first = false;
										}
									}
								}
							}
							skipFirstCheck = false;
						} else
							e.ebp = val;
						var prev = stack[stack.length - 1];
						var ordered = prev == null || prev.ebp == null || e.ebp > prev.ebp;
						if( !ordered && !(inProlog && (i << 3) == prologPos) ) continue;
						stack.push(e);
						atGap = fromNative(e);
						if( max > 0 && stack.length >= max ) return stack;
					}
				}
			}
		} else {
			var stackBottom = esp.toInt();
			var stackTop = tinf.stackTop.toInt();
			for( i in 0...size >> 2 ) {
				var val = mem.getI32(i << 2);
				if( val > stackBottom && val < stackTop || (inProlog && (i << 2) == prologPos) ) {
					var codePtr = mem.getPointer((i + 1) << 2, jit.align);
					var e = jit.resolveAsmPos(codePtr);
					if( e != null && e.fpos >= 0 ) {
						e.ebp = Pointer.make(val,0);
						stack.push(e);
						if( max > 0 && stack.length >= max ) return stack;
					}
				}
			}
		}

		return [for( s in stack ) if( s.fidx == Eval.TRAMPOLINE_FIDX || isValidRaw(s) ) s];
	}

	inline function get_stackFrameCount() return currentStack.length;

	public function getBackTrace() : Array<StackInfo> {
		return [for( e in currentStack ) stackInfo(e)];
	}

	public function getStackFrame( ?frame ) : StackInfo {
		if( frame == null ) frame = currentStackFrame;
		var f = currentStack[frame];
		if( f == null )
			return { file : "???", line : 0, ebp : Pointer.make(0, 0), context : null };
		return stackInfo(f);
	}

	public function getClosureStack( value ) : Array<StackInfo> {
		var stack = @:privateAccess eval.getClosureStack(value);
		var out = [];
		for( ptr in stack ) {
			var e = jit.resolveAsmPos(ptr);
			if( e == null || e.fpos < 0 ) continue;
			var owner = e.module == null ? module : e.module;
			if( !owner.isValid(e.fidx,e.fpos) ) continue;
			e.ebp = null;
			out.push(stackInfo(e));
		}
		return out;
	}

	function stackInfo( f ) : StackInfo {
		if( f.fidx == Eval.TRAMPOLINE_FIDX )
			return { file : "<native>", line : 0, column : 0, endLine : 0, endColumn : 0, sourceHash : 0, start : -1, end : -1, ebp : f.ebp, context : null, functionName : null };
		var owner : Module = f.module == null ? module : f.module;
		var s = owner.resolveSymbol(f.fidx, f.fpos);
		return { file : s.file, line : s.line, column : s.column, endLine : s.endLine, endColumn : s.endColumn, sourceHash : s.sourceHash,
			start : s.start, end : s.end, ebp : f.ebp, context : owner.getMethodContext(f.fidx), functionName : owner.getFunctionDebugName(f.fidx) };
	}

	function setContext(global:Bool) {
		var cur = currentStack[currentStackFrame];
		if( cur == null || cur.fidx == Eval.TRAMPOLINE_FIDX ) return false;
		var ownerModule = cur.module == null ? module : cur.module;
		var ownerJit = cur.jit == null ? jit : cur.jit;
		var ownerEval = evalByModule.get(ownerModule);
		if( ownerEval == null ) ownerEval = makeEval(ownerModule, ownerJit);
		eval = ownerEval;
		eval.currentThread = currentThread;
		eval.globalContext = global;
		var children = [for( i in 0...currentStackFrame ) currentStack[currentStackFrame - 1 - i]];
		eval.setContext(cur.fidx, cur.fpos, ownerJit.getNativeCodePos(cur.codePos), cur.ebp, children);
		return true;
	}

	public function getValue( expr : String, global = false ) : Value {
		if( !setContext(global) )
			return null;
		var v = eval.eval(expr);
		eval.globalContext = false;
		return v;
	}

	public function setValue( expr : String, value : String, global = false ) : Value {
		if( !setContext(global) )
			return null;
		return eval.setValue(expr, value);
	}

	public function getRef( expr : String, global = false ) : Address {
		if( !setContext(global) )
			return null;
		var v = eval.ref(expr);
		eval.globalContext = global;
		return v;
	}

	public function getWatches() {
		return [for( w in watches ) w.addr];
	}

	public function watch( a : Address, forReadWrite = false ) {
		var size = jit.align.typeSize(a.t);
		var availableRegs = HW_REGS.copy();
		for( w in watches )
			for( r in w.regs )
				availableRegs.remove(r.r);
		var w : WatchPoint = {
			addr : a,
			regs : [],
			forReadWrite : forReadWrite,
		};
		var offset = 0;
		var bitSize = [1, 2, 8, 4];
		while( size > 0 ) {
			var r = availableRegs.shift();
			if( r == null )
				throw "Not enough hardware register to watch: remove previous watches";
			var v = if( size >= 8 ) 2 else if( size >= 4 ) 3 else if( size >= 2 ) 1 else 0;
			w.regs.push({ r : r, offset : offset, bits : v });
			var delta = bitSize[v];
			size -= delta;
			offset += delta;
		}
		watches.push(w);
		syncDebugRegs();
		return w;
	}

	public function unwatch( a : Address ) {
		for( w in watches )
			if( w.addr == a ) {
				watches.remove(w);
				syncDebugRegs();
				return true;
			}
		return false;
	}


	function syncDebugRegs() {
		var wasPaused = false;
		if( currentThread == null ) {
			pause();
			wasPaused = true;
		}
		var dr7 = 0x100;
		for( w in watches ) {
			for( r in w.regs ) {
				var rid = HW_REGS.indexOf(r.r);
				dr7 |= 1 << (rid * 2);
				dr7 |= ((w.forReadWrite ? 3 : 1) | (r.bits << 2)) << (16 + rid * 4);
			}
		}
		api.writeRegister(currentThread, Dr7, Pointer.make(dr7, 0));
		for( w in watches )
			for( r in w.regs )
				api.writeRegister(currentThread, r.r, w.addr.ptr.offset(r.offset));
		if( wasPaused )
			resume();
	}

	function getCodePos(tid) {
		var eip = getReg(tid, Eip);
		return eip;
	}

	public function resume() {
		if( stoppedThread == null )
			throw "No thread stopped";
		if( DEBUG ) trace("RUN " + jit.codePtrToString(getCodePos(currentThread)));
		if( !api.resume(stoppedThread) && !processExit )
			throw "Could not resume "+stoppedThread;
		stoppedThread = null;
		watchBreak = null;
	}

	public function end() {
		// Teardown also runs after the target has exited or been killed. Resume it
		// when possible, but do not turn an already-gone process into an adapter
		// exception.
		if( stoppedThread != null ) {
			api.resume(stoppedThread);
			stoppedThread = null;
		}
		if( api != null ) {
			api.stop();
			api = null;
		}
	}

	function tryReadMem( addr : Pointer, size : Int ) : Null<Buffer> {
		var mem = new Buffer(size);
		return api.read(addr, mem, size) ? mem : null;
	}

	function readMem( addr : Pointer, size : Int ) {
		var mem = tryReadMem(addr, size);
		if( mem == null )
			throw "Failed to read memory @" + addr.toString() + "[" + size+"]";
		return mem;
	}

	function findReadableBase( addr : Pointer, size : Int ) {
		var ptr = jit.align.ptr;
		var min = 0, max = Std.int(size / ptr);
		while( min < max ) {
			var mid = (min + max) >> 1;
			if( tryReadMem(addr.offset(mid * ptr), size - mid * ptr) != null ) max = mid else min = mid + 1;
		}
		return min * ptr;
	}

	function getAsm( ptr : Pointer ) {
		if( !jit.isCodePtr(ptr) )
			throw "Assert invalid ptr " + ptr;
		return api.readByte(ptr, 0);
	}

	function setAsm( ptr : Pointer, byte : Int ) {
		if( !jit.isCodePtr(ptr) )
			throw "Assert invalid ptr " + ptr;
		if( DEBUG ) trace('Set ${jit.codePtrToString(ptr)}=$byte');
		api.writeByte(ptr, 0, byte);
		if( !api.flush(ptr, 1) )
			throw "Failed to flush code @" + ptr.toString();
		var actual = api.readByte(ptr, 0);
		if( actual != (byte & 0xFF) )
			throw 'Failed to verify code write @${ptr.toString()}: expected ${byte & 0xFF}, got $actual';
		DebugTrace.write("debugger", "code_write", { address : ptr.toString(), value : byte & 0xFF, verified : actual });
	}

	function getReg(tid, reg) {
		return Pointer.ofPtr(api.readRegister(tid, reg));
	}

	function setReg(tid, reg, value) {
		if( !api.writeRegister(tid, reg, value) )
			throw "Failed to set register " + reg;
	}

	public function checkBreakpointLine(file : String, line : Int) {
		for( owner in allJitModules() ) {
			var breaks = owner.module.getBreaks(file, line);
			if( breaks != null ) return breaks.line;
		}
		return -1;
	}

	public function checkBreakpointLocation(file : String, line : Int, ?column : Int) {
		for( owner in allJitModules() ) {
			var breaks = owner.module.getBreaks(file, line, column);
			if( breaks == null || breaks.breaks.length == 0 ) continue;
			var point = breaks.breaks[0], symbol = owner.module.resolveSymbol(point.ifun, point.pos);
			return {line:breaks.line, column:symbol.column, endLine:symbol.endLine, endColumn:symbol.endColumn,
				sourceHash:symbol.sourceHash, start:symbol.start, end:symbol.end};
		}
		return null;
	}

	public function getBreakpointLocations(file:String, line:Int, ?column:Int, ?endLine:Int, ?endColumn:Int) {
		var result = [], seen = new Map<String,Bool>();
		for( owner in allJitModules() ) {
			var locations = owner.module.getBreakpointLocations(file, line, column, endLine, endColumn);
			if( locations == null ) continue;
			for( location in locations ) {
				if( !owner.hasFunction(location.ifun) ) continue;
				var key = location.line + ":" + location.column + ":" + location.endLine + ":" + location.endColumn;
				if( seen.exists(key) ) continue;
				seen.set(key, true);
				result.push({line:location.line, column:location.column, endLine:location.endLine, endColumn:location.endColumn,
					sourceHash:location.sourceHash});
			}
		}
		result.sort(function(a, b) {
			if( a.line != b.line ) return a.line - b.line;
			if( a.column != b.column ) return a.column - b.column;
			if( a.endLine != b.endLine ) return a.endLine - b.endLine;
			return a.endColumn - b.endColumn;
		});
		return result;
	}

	public function addBreakpoint( file : String, line : Int, condition : Null<String>, ?column : Int ) {
		var resolvedLine = -1;
		var installed = false;
		for( owner in allJitModules() ) {
			var breaks = owner.module.getBreaks(file, line, column);
			if( breaks == null ) continue;
			resolvedLine = breaks.line;
			for( b in breaks.breaks ) {
				if( !owner.hasFunction(b.ifun) ) continue;
				var found = false;
				for( a in breakPoints ) {
					if( a.jit == owner && a.fid == b.ifun && a.pos == b.pos ) {
						found = true;
						break;
					}
				}
				if( found ) { installed = true; continue; }
				var codePos = owner.getCodePos(b.ifun, b.pos);
				var old = getAsm(codePos);
				setAsm(codePos, INT3);
				breakPoints.push({ fid : b.ifun, pos : b.pos, oldByte : old, codePos : codePos, condition : condition, jit : owner, module : owner.module, stableId : owner.module.getStableFunctionId(b.ifun) });
				DebugTrace.write("debugger", "breakpoint_installed", { file : file, line : breaks.line, functionId : b.ifun, opcode : b.pos, address : codePos.toString(), oldByte : old });
				installed = true;
			}
		}
		return installed ? resolvedLine : -1;
	}

	public function addFunctionBreakpoint( name : String, condition : Null<String> ) : { verified : Bool, message : Null<String> } {
		var exact = [];
		var unqualified = [];
		for( owner in allJitModules() )
			for( candidate in owner.module.getNamedFunctions() ) {
				if( candidate.name == name ) exact.push({ owner : owner, candidate : candidate });
				if( candidate.field == name ) unqualified.push({ owner : owner, candidate : candidate });
			}
		var matches = exact.length > 0 ? exact : unqualified;
		if( matches.length == 0 ) return { verified : false, message : 'Function "$name" was not found' };
		if( exact.length == 0 && matches.length > 1 ) {
			var names = [for( match in matches ) match.candidate.name];
			names.sort(Reflect.compare);
			return { verified : false, message : 'Function "$name" is ambiguous: ' + names.join(", ") };
		}
		var installed = false;
		var sourceConflict = false;
		for( match in matches ) {
			var owner = match.owner;
			var candidate = match.candidate;
			if( !owner.hasFunction(candidate.ifun) || owner.module.code.functions[candidate.ifun].debug.length == 0 ) continue;
			var codePos = owner.getCodePos(candidate.ifun, 0);
			var existing = Lambda.find(breakPoints, bp -> bp.jit == owner && bp.fid == candidate.ifun && bp.pos == 0);
			if( existing != null ) {
				if( existing.functionBreakpoint == true ) installed = true;
				else sourceConflict = true;
				continue;
			}
			var old = getAsm(codePos);
			setAsm(codePos, INT3);
			breakPoints.push({ fid : candidate.ifun, pos : 0, oldByte : old, codePos : codePos, condition : condition, jit : owner, module : owner.module, stableId : candidate.stableId, functionBreakpoint : true });
			DebugTrace.write("debugger", "function_breakpoint_installed", { name : candidate.name, functionId : candidate.ifun, address : codePos.toString(), oldByte : old });
			installed = true;
		}
		if( !installed && sourceConflict )
			return { verified : false, message : 'Function "$name" conflicts with a source breakpoint at its entry' };
		return installed ? { verified : true, message : null } : { verified : false, message : 'Function "$name" has no executable debug mapping' };
	}

	public function clearFunctionBreakpoints() {
		for( bp in breakPoints.copy() )
			if( bp.functionBreakpoint == true ) removeBP(bp);
	}

	function allJitModules():Array<JitInfo> return [jit].concat(jit.debugModules);
	inline function isValidRaw(s:StackRawInfo) {
		var owner = s.module == null ? module : s.module;
		return owner.isValid(s.fidx, s.fpos);
	}

	public function clearBreakpoints( file : String ) {
		for( owner in allJitModules() ) {
			var ffuns = owner.module.getFileFunctions(file);
			if( ffuns == null ) continue;
			for( b in breakPoints.copy() )
				for( f in ffuns.functions )
					if( b.jit == owner && b.fid == f.ifun ) { removeBP(b); break; }
		}
	}

	function removeBP( bp ) {
		breakPoints.remove(bp);
		setAsm(bp.codePos, bp.oldByte);
		if( nextStep == bp.codePos ) {
			singleStep(currentThread, false);
			nextStep = Pointer.make(0, 0);
		}
	}

	public function removeBreakpoint( file : String, line : Int ) {
		var rem = false;
		for( owner in allJitModules() ) {
			var breaks = owner.module.getBreaks(file, line);
			if( breaks == null ) continue;
			for( b in breaks.breaks ) for( a in breakPoints.copy())
				if( a.jit == owner && a.fid == b.ifun && a.pos == b.pos ) { rem = true; removeBP(a); break; }
		}
		return rem;
	}

	function set_breakOnThrow(b) {
		var count = eval.readI32(jit.threads);
		var tinfos = eval.readPointer(jit.threads.offset(8));
		var flagsPos = jit.align.ptr * 6 + 8;
		for( i in 0...count ) {
			var tinf = eval.readPointer(tinfos.offset(jit.align.ptr * i));
			var flags = eval.readI32(tinf.offset(flagsPos));
			if( b ) flags |= 2 else flags &= ~2;
			eval.writeI32(tinf.offset(flagsPos), flags);
		}
		return breakOnThrow = b;
	}

}
