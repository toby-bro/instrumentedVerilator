class Dummy;
  int val;
  function new();
    val = 0;
  endfunction
endclass
module casex_example(input  logic [3:0] in, output logic     out);
  always_comb begin
    casex (in)
      4'b1x0?: out = 1;
      4'bx1Z0: out = 0;
      default: out = in[0];
    endcase
  end
endmodule
module casez_example(input  logic [3:0] in, output logic     out);
  always_comb begin
    casez (in)
      4'b1?0z: out = 1;
      4'bzz11: out = 0;
      default: out = in[1];
    endcase
  end
endmodule
module case_constant_x(input  logic [1:0] in, output logic     out);
  always_comb begin
    case (in)
      2'b1X: out = 1;
      2'b01: out = 0;
      default: out = 0;
    endcase
  end
endmodule
module unique_enum_case(input  logic [1:0] in, output logic [7:0] out);
  typedef enum logic [1:0] {E0=2'b00, E1=2'b01, E2=2'b10, E3=2'b11} Etype;
  Etype state;
  always_comb begin
    state = Etype'(in);
    unique case (state)
      E0: out = 8'h00;
      E1: out = 8'h11;
      E2: out = 8'h22;
      E3: out = 8'h33;
    endcase
  end
endmodule
module inside_range_case(input  logic [3:0] in, output logic [1:0] out);
  always_comb begin
    case (in)
      inside {[0:3],5}:    out = 2'b00;
      inside {4,[6:9]}:    out = 2'b01;
      default:             out = 2'b10;
    endcase
  end
endmodule
module simple_case_fast(input  logic [1:0] in, output logic [1:0] out);
  always_comb begin
    case (in)
      2'b00: out = 2'b10;
      2'b01: out = 2'b11;
      default: out = 2'b00;
    endcase
  end
endmodule
module complicated_case(input  logic [16:0] in, output logic     out);
  always_comb begin
    case (in)
      17'b00000000000000000: out = 0;
      17'b00000000000000001: out = 1;
    endcase
  end
endmodule
module bit_select_module(input  logic [7:0] in, output logic     out);
  assign out = in[3];
endmodule
module bit_equality_module(input  logic [3:0] a, b, output logic eq, ne);
  assign eq = (a == b);
  assign ne = (a != b);
endmodule
module class_instantiation_module(input  logic clk, reset, output logic flag);
  always_ff @(posedge clk) begin
    Dummy d = new();
    flag <= reset;
  end
endmodule
