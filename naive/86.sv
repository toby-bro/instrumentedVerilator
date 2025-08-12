module mod_params_gen#(parameter WIDTH=8, parameter DEPTH=4)(input logic clk, input logic [WIDTH-1:0] din, output logic [WIDTH-1:0] dout);
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  genvar idx;
  generate
    for (idx=0; idx<DEPTH; idx=idx+1) begin : shift_reg
      if (idx==0) assign mem[idx] = din;
      else        assign mem[idx] = mem[idx-1];
    end
  endgenerate
  assign dout = mem[DEPTH-1];
endmodule
module mod_enum_case(input logic clk, input logic [1:0] sel, input logic [7:0] in0, input logic [7:0] in1, input logic [7:0] in2, input logic [7:0] in3, output logic [7:0] out);
  typedef enum logic [1:0] {ID0=2'd0, ID1=2'd1, ID2=2'd2, ID3=2'd3} sel_e;
  sel_e curr;
  always_ff @(posedge clk) curr <= sel_e'(sel);
  always_comb begin
    case (curr)
      ID0:   out = in0;
      ID1:   out = in1;
      ID2:   out = in2;
      default: out = in3;
    endcase
  end
endmodule
module mod_struct_union(input logic clk, input logic [15:0] data_in, output logic [7:0] high, output logic [7:0] low);
  typedef struct packed { logic [7:0] lo; logic [7:0] hi; } pair_t;
  typedef union packed  { logic [15:0] full; pair_t p; } u_t;
  u_t ureg;
  always_ff @(posedge clk) ureg.full <= data_in;
  assign high = ureg.p.hi;
  assign low  = ureg.p.lo;
endmodule
module mod_class_inst(input logic clk, input logic rst, input logic [7:0] din, output logic [7:0] dout);
  class accumulator;
    rand logic [7:0] acc;
    function void init();   acc = '0;        endfunction
    function void update(input logic [7:0] v); acc += v; endfunction
    function logic [7:0] value();               return acc; endfunction
  endclass
  accumulator acc_inst;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      acc_inst = new;
      acc_inst.init();
    end else begin
      acc_inst.update(din);
    end
  end
  always_comb begin
    dout = acc_inst.value();
  end
endmodule
module mod_dynamic_array(input logic clk, input logic en, input logic [7:0] din, output logic [7:0] dout);
  logic [7:0] arr[$];
  always_ff @(posedge clk) begin
    if (en)               arr.push_back(din);
    else if (arr.size()>0) arr.pop_back();
  end
  always_comb begin
    if (arr.size()>0) dout = arr[arr.size()-1];
    else              dout = '0;
  end
endmodule
module mod_function(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum);
  function automatic logic [4:0] add(input logic [3:0] x, input logic [3:0] y);
    add = x + y;
  endfunction
  assign sum = add(a,b);
endmodule
module mod_generate_bus(input logic [7:0] inbus, output logic [7:0] outbus);
  genvar j;
  generate
    for (j=0; j<8; j=j+1) begin : bit_loop
      assign outbus[j] = inbus[j] ^ 1'b1;
    end
  endgenerate
endmodule
