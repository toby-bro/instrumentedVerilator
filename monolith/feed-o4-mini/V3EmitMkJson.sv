module debug_module(input logic enable, output logic debug_out);
  logic tmp;
  function void _ZL5debugv();
    tmp = enable;
  endfunction
  always_comb begin
    if (enable) _ZL5debugv();
    debug_out = tmp;
  end
endmodule
module printer_ctor(input logic clk, output logic ready);
  class Printer;
    string fname;
    function new(string f);
      fname = f;
    endfunction
    function string get_name();
      return fname;
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p = new("output.json");
    ready <= 1;
  end
endmodule
module printer_dtor(input logic clk, input logic rst, output logic done);
  class Printer;
    function void cleanup();
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) done <= 0;
    else begin
      p.cleanup();
      done <= 1;
    end
  end
endmodule
module printer_begin_str(input logic clk, input logic rst, output logic active);
  class Printer;
    function void begin_str(string key, string bracket);
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) active <= 0;
    else begin
      p.begin_str("system", "{");
      active <= 1;
    end
  end
endmodule
module printer_put_str(input logic clk, output logic valid);
  class Printer;
    function void put_str(string key, string val);
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p.put_str("prefix", "json");
    valid <= 1;
  end
endmodule
module printer_put_bool(input logic clk, output logic success);
  class Printer;
    function void put_bool(string key, bit val);
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p.put_bool("coverage", 1'b1);
    success <= 1'b1;
  end
endmodule
module printer_put_int(input logic clk, output integer code);
  class Printer;
    function void put_int(string key, int val);
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p.put_int("version", 32'd1);
    code <= 0;
  end
endmodule
module printer_begin_char(input logic clk, output logic opened);
  class Printer;
    function void begin_char(string key, byte c);
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p.begin_char("submodules", 8'h5B);
    opened <= 1;
  end
endmodule
module printer_putList(input logic clk, output logic list_ok);
  class Printer;
    function void putList(string key, string list[]);
    endfunction
  endclass
  Printer p;
  string arr[3] = '{ "a", "b", "c" };
  always_ff @(posedge clk) begin
    p.putList("deps", arr);
    list_ok <= 1;
  end
endmodule
module printer_end(input logic clk, output logic closed);
  class Printer;
    function void end_printer();
    endfunction
  endclass
  Printer p;
  always_ff @(posedge clk) begin
    p.end_printer();
    closed <= 1;
  end
endmodule
module emit_manifest(input logic clk, output logic done);
  class Emitter;
    function void emitManifest();
    endfunction
    function void execute();
      emitManifest();
    endfunction
  endclass
  Emitter e;
  always_ff @(posedge clk) begin
    e = new();
    e.execute();
    done <= 1;
  end
endmodule
module v3emit_mkjson_emit(input logic enable, output logic finished);
  class V3EmitMkJson;
    function void emit();
    endfunction
  endclass
  V3EmitMkJson inst;
  always_comb begin
    if (enable) inst.emit();
    finished = enable;
  end
endmodule
