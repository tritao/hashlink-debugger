package hld;

/** Opt-in JSONL diagnostics shared by the debugger and DAP adapter. */
class DebugTrace {
	public static function enabled():Bool {
		return Sys.getEnv("HL_DEBUG_TRACE") != null;
	}

	public static function write(component:String, event:String, ?fields:Dynamic):Void {
		#if hxnodejs
		var path = Sys.getEnv("HL_DEBUG_TRACE");
		if( path == null || path.length == 0 ) return;
		var record:Dynamic = fields == null ? {} : fields;
		Reflect.setField(record, "timestamp", Date.now().toString());
		Reflect.setField(record, "monotonic", haxe.Timer.stamp());
		Reflect.setField(record, "component", component);
		Reflect.setField(record, "event", event);
		try js.node.Fs.appendFileSync(path, haxe.Json.stringify(record) + "\n") catch( _:Dynamic ) {}
		#end
	}
}
