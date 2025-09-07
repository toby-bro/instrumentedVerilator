module SVClassRefUse(input logic [7:0] in, output logic [7:0] out);
  class CRef;
    rand logic [7:0] d;
    function new(); endfunction
  endclass
  CRef cref;
  always_comb begin
    cref = new();
    cref.d = in;
    out = cref.d;
  end
endmodule
module SVStructUnionUse(input logic [15:0] in, output logic [3:0] out_lo);
  typedef struct packed {
    logic [7:0] b0;
    logic [7:0] b1;
  } struct_t;
  typedef union packed {
    logic [15:0] whole;
    struct {
      logic [7:0] low;
      logic [7:0] high;
    } parts;
  } union_t;
  always_comb begin
    struct_t s;
    union_t u;
    s.b0 = in[7:0];
    s.b1 = in[15:8];
    u.parts.low = s.b0;
    u.parts.high = s.b1;
    out_lo = u.parts.low[3:0];
  end
endmodule
module SVFunctionUse(input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum);
  function logic [4:0] add(input logic [3:0] x, input logic [3:0] y);
    logic [4:0] tmp;
    begin
      tmp = x + y;
      return tmp;
    end
  endfunction
  always_comb sum = add(a, b);
endmodule
module SVTaskCall(input logic clk, input logic rst, output logic [3:0] q_out);
  logic [3:0] q;
  task seq_logic(input logic in1, input logic in2, output logic [3:0] out1);
    integer i;
    begin
      for (i = 0; i < 4; i = i + 1)
        out1[i] = in1 & in2;
    end
  endtask
  always_ff @(posedge clk or posedge rst) begin
    if (rst)
      q <= 0;
    else
      seq_logic(clk, rst, q);
  end
  always_comb q_out = q;
endmodule
module SVGenerateCell(input logic [1:0] sel, output logic [1:0] out);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : gencells
      assign out[i] = sel[i];
    end
  endgenerate
endmodule
module SVTypedefEnumUse(input logic en, input logic [1:0] sel, output logic ok);
  typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_t;
  state_t state;
  always_comb begin
    if (en)
      state = BUSY;
    else
      state = IDLE;
    ok = (state == sel);
  end
endmodule
module SVGenericNode(input logic [7:0] in, output logic outflag);
  logic flag;
  logic [7:0] tmp;
  always_comb begin
    tmp = in;
    if (tmp > 128) begin
      flag = 1;
    end else if (tmp > 64) begin
      flag = 0;
    end else begin
      flag = in[0];
    end
  end
  assign outflag = flag;
endmodule
module SVCellUse(input logic [3:0] a, output logic [3:0] b);
  always_comb begin
    case (a)
      4'd0: b = 4'd1;
      4'd1: b = 4'd2;
      default: b = a;
    endcase
  end
endmodule
