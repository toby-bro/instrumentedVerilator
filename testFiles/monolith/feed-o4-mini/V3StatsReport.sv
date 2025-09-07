module sumit_mod(input logic clk, input logic en, output logic done);
  covergroup sumit_cg @(posedge clk);
    cp : coverpoint en { bins zero = {0}; bins one = {1}; }
  endgroup
  sumit_cg cg;
  always_ff @(posedge clk) begin
    cg.sample();
    if (en) done <= 1;
    else done <= 0;
  end
endmodule
module stars_mod(input logic clk, input logic a, output logic b);
  covergroup stars_cg @(posedge clk);
    cp1 : coverpoint a { bins low = {1'b0}; bins high = {1'b1}; }
    cp2 : coverpoint b iff (a) { bins one = {1'b1}; }
  endgroup
  stars_cg cg1;
  always_ff @(posedge clk) begin
    cg1.sample();
    b <= a;
  end
endmodule
module stages_mod(input logic clk, input logic [1:0] sel, output logic [1:0] out);
  covergroup cg_stage @(posedge clk);
    cp0 : coverpoint sel[0] { bins bz = {1'b0}; bins bo = {1'b1}; }
    cp1 : coverpoint sel[1] { bins cz = {1'b0}; bins co = {1'b1}; }
  endgroup
  cg_stage cg;
  always_ff @(posedge clk) begin
    cg.sample();
    out <= sel;
  end
endmodule
module getstat_sum_mod(input logic [7:0] in, output logic [15:0] sum);
  function automatic int unsigned get_val(input logic [7:0] v);
    return v + 1;
  endfunction
  assign sum = get_val(in);
endmodule
module infoheader_mod(input logic clk, input string s, output logic ok);
  class InfoCls;
    string msg;
    function new(string str);
      msg = {str, "_info"};
    endfunction
    function string getmsg();
      return msg;
    endfunction
  endclass
  InfoCls ic;
  always_ff @(posedge clk) begin
    ic = new(s);
    ok <= (ic.getmsg() == {s, "_info"});
  end
endmodule
module stats_report_mod(input logic clk, output logic val);
  covergroup cg_rep @(posedge clk);
    cp : coverpoint clk;
  endgroup
  cg_rep cr;
  always_ff @(posedge clk) begin
    cr.sample();
    val <= 1;
  end
endmodule
module summary_report_mod(input logic clk, output logic [31:0] cnt);
  covergroup cgsum @(posedge clk);
    cp1 : coverpoint cnt { bins low = {0}; bins high = {[1:32'hffffffff]}; }
    cp2 : coverpoint cnt[0] { bins z = {1'b0}; bins o = {1'b1}; }
  endgroup
  cgsum cgs;
  always_ff @(posedge clk) begin
    cgs.sample();
    cnt <= cnt + 1;
  end
endmodule
module addstat_mod(input logic clk, input logic flag, output logic done);
  class StatAdder;
    int x;
    function new(int v);
      x = v;
    endfunction
    function int get();
      return x;
    endfunction
  endclass
  StatAdder sa;
  always_ff @(posedge clk) begin
    sa = new(flag);
    done <= sa.get();
  end
endmodule
module ctor_mod(input logic clk, input logic in, output logic out);
  class CtorCls;
    bit v;
    function new(bit a);
      v = a;
    endfunction
    function bit getv();
      return v;
    endfunction
  endclass
  CtorCls obj;
  always_ff @(posedge clk) begin
    obj = new(in);
    out <= obj.getv();
  end
endmodule
module dump_mod(input logic clk, input logic [3:0] d, output logic [3:0] q);
  class DumpCls;
    bit [3:0] v;
    function new(bit [3:0] x);
      v = x;
    endfunction
    function bit [3:0] get();
      return v;
    endfunction
  endclass
  DumpCls dc;
  always_ff @(posedge clk) begin
    dc = new(d);
    q <= dc.get();
  end
endmodule
