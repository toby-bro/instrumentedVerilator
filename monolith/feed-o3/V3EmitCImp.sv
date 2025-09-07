package sv_feature_pkg;
  typedef struct packed {
    logic [7:0] fieldA;
    logic [7:0] fieldB;
  } packed_s;
  typedef struct {
    logic [7:0] fieldA;
    logic [7:0] fieldB;
  } unpacked_s;
  typedef enum logic [1:0] {IDLE, BUSY, DONE} state_e;
endpackage
import sv_feature_pkg::*;
//----------------------------------------------------------------------
module class_mod (
    input  logic        clk,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
  class my_c;
    int val;
    function new(); val = 0; endfunction
    function int inc (int a); val += a; return val; endfunction
  endclass
  my_c obj;
  initial begin
    obj = new();              
  end
  function automatic void track();
    static int call_count = 0;
    call_count++;
  endfunction
  always_ff @(posedge clk) begin
    track();
    out_data <= obj.inc(in_data);   
  end
  string greet;
  initial greet = "hello";
endmodule
//----------------------------------------------------------------------
module struct_mod (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
  unpacked_s us;
  packed_s   ps;
  event ev;
  initial -> ev;  
  always_comb begin
    us.fieldA   = in_data;    
    ps.fieldB   = us.fieldA;  
    out_data    = ps.fieldB;
  end
endmodule
//----------------------------------------------------------------------
module coverage_mod (
    input  logic       clk,
    input  logic [7:0] sig,
    output logic       dummy
);
  covergroup cg @(posedge clk);
    coverpoint sig;
  endgroup
  cg cg_inst = new();
  property p_data; @(posedge clk) sig[0]; endproperty
  cover property (p_data);
  assign dummy = sig;
endmodule
//----------------------------------------------------------------------
module dpi_mod (
    input  logic [31:0] din,
    output logic [31:0] dout
);
  import "DPI-C" function int cfunc (input int a);
  assign dout = cfunc(din);
endmodule
//----------------------------------------------------------------------
module dump_mod (
    input  logic clk,
    output logic dout
);
  initial begin
    $dumpfile("dump.vcd");     
    $dumpvars(0, dump_mod);
    $timeformat(-9, 1, " ns", 0);  
    $printtimescale;                
  end
  assign dout = clk;
endmodule
