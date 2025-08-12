module comb_adder(input  logic [3:0] a, b, output logic [4:0] sum);
  assign sum = a + b;
endmodule
module seq_counter(input  logic clk, reset, output logic [3:0] count);
  always_ff @(posedge clk or posedge reset) begin
    if (reset) count <= 0;
    else        count <= count + 1;
  end
endmodule
module param_module #(parameter N = 8) (input  logic [N-1:0] in, output logic [N-1:0] out);
  assign out = in;
endmodule
module gen_module(input  logic en, output logic [7:0] out);
  genvar i;
  generate
    for (i = 0; i < 8; i = i + 1) begin : gen_bits
      assign out[i] = en;
    end
  endgenerate
endmodule
module struct_enum_module(input  logic [1:0] sel, output logic [3:0] y);
  typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
  typedef struct packed { logic a; logic [2:0] b; } my_struct;
  state_t s;
  my_struct st;
  always_comb begin
    case (sel)
      S0: begin
        st = '{a:1, b:3};
        y  = {st.a, st.b};
      end
      S1: y = st.a ? 4'hF : 4'h0;
      S2: y = 4'h5;
      default: y = 4'b1010;
    endcase
  end
endmodule
interface simple_if(input logic clk);
  logic [3:0] data;
  modport master (input clk, output data);
endinterface
module interface_module(input  logic clk, rst, output logic [3:0] dout);
  simple_if inst_if(.clk(clk));
  always_ff @(posedge clk or posedge rst) begin
    if (rst)          inst_if.data <= 0;
    else              inst_if.data <= inst_if.data + 1;
  end
  assign dout = inst_if.data;
endmodule
module class_module(input  logic clk, rst, output logic out);
  class my_class;
    rand logic val;
    function void do_something();
      val = !val;
    endfunction
  endclass
  my_class cls;
  always_ff @(posedge clk or posedge rst) begin
    if (rst)       cls = new();
    else           cls.do_something();
    out <= cls.val;
  end
endmodule
module cover_module(input  logic [7:0] data, output logic flag);
  covergroup cg @(posedge data[0]);
    coverpoint data;
  endgroup
  cg inst_cg = new();
  always_comb begin
    flag = |data;
  end
endmodule
module generate_if #(parameter FLAG = 1) (input logic a, b, output logic y);
  generate
    if (FLAG) begin
      assign y = a & b;
    end else begin
      assign y = a | b;
    end
  endgenerate
endmodule
module function_module(input  logic [3:0] a, b, output logic [4:0] res);
  function automatic logic [4:0] add(input logic [3:0] x, y);
    add = x + y;
  endfunction
  assign res = add(a, b);
endmodule
module multiarray_module(input  logic       clk,
                         input  logic [1:0] idx,
                         output logic [7:0] dout);
  logic [7:0] mem [0:3];
  always_ff @(posedge clk) begin
    mem[idx] <= mem[idx] + 1;
  end
  assign dout = mem[idx];
endmodule
