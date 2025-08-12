interface simple_if(input logic clk, input logic rst);
  logic [7:0] data;
  modport IN (input data, clk, rst);
endinterface
module alu #(parameter WIDTH = 8) (
  input  logic [WIDTH-1:0] a,
  input  logic [WIDTH-1:0] b,
  input  logic             sub,
  output logic [WIDTH-1:0] y,
  output logic             c_out
);
  always_comb begin
    {c_out, y} = sub ? (a - b) : (a + b);
  end
endmodule
module struct_union (
  input  logic       sel,
  input  logic [3:0] in1,
  input  logic [3:0] in2,
  output logic [3:0] out_union,
  output logic [3:0] out_struct
);
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } st_t;
  typedef union packed {
    st_t         s;
    logic [7:0]  raw;
  } u_t;
  always_comb begin
    u_t u;
    if (sel) begin
      u.raw      = {in1, in2};
      out_struct = u.s.hi;
    end else begin
      u.s        = '{hi: in1, lo: in2};
      out_union  = u.raw[3:0];
    end
  end
endmodule
module fsm (
  input  logic       clk,
  input  logic       reset,
  input  logic       in,
  output logic       out_state
);
  typedef enum logic [1:0] { IDLE, BUSY, DONE } state_t;
  state_t state, next_state;
  always_ff @(posedge clk) begin
    if (reset)
      state <= IDLE;
    else
      state <= next_state;
  end
  always_comb begin
    next_state = state;
    case (state)
      IDLE: if (in) next_state = BUSY;
      BUSY:         next_state = DONE;
      DONE:         next_state = IDLE;
      default:      next_state = IDLE;
    endcase
  end
  always_comb begin
    out_state = (state == DONE);
  end
endmodule
module use_if (
  input  logic       clk,
  input  logic       rst,
  input  logic [7:0] din,
  output logic [7:0] dout
);
  simple_if if_inst(.clk(clk), .rst(rst));
  always_comb begin
    if_inst.data = din;
    dout = if_inst.data + 8'd1;
  end
endmodule
module class_test (
  input  logic       clk,
  input  logic       reset,
  input  logic [3:0] val,
  output logic [3:0] out_val
);
  class my_class;
    rand logic [3:0] x;
    function logic [3:0] inc(input logic [3:0] v);
      return v + 4'd1;
    endfunction
  endclass
  always_ff @(posedge clk) begin
    if (reset)
      out_val <= 4'd0;
    else begin
      static my_class obj;
      if (obj == null)
        obj = new();
      obj.x      = val;
      out_val    <= obj.inc(obj.x);
    end
  end
endmodule
module gen_array #(parameter N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] c,
  output logic         any_high
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign c[i] = a[i] & b[i];
    end
  endgenerate
  assign any_high = |c;
endmodule
module fun_task (
  input  logic       clk,
  input  logic       start,
  input  logic [3:0] in,
  output logic [3:0] result,
  output logic       done
);
  function automatic logic [3:0] mul2(input logic [3:0] x);
    return x << 1;
  endfunction
  task automatic perform(input logic [3:0] v, output logic [3:0] out, output logic status);
    out    = mul2(v);
    status = 1;
  endtask
  always_ff @(posedge clk) begin
    if (start) begin
      perform(in, result, done);
    end else
      done <= 0;
  end
endmodule
module param_case #(parameter TYPE = 0) (
  input  logic [7:0] data,
  output logic [7:0] out
);
  always_comb begin
    case (TYPE)
      0:       out = data;
      1:       out = ~data;
      default: out = data ^ 8'hFF;
    endcase
  end
endmodule
module assert_mod (
  input  logic       clk,
  input  logic       reset,
  input  logic [3:0] din,
  output logic       error
);
  always_ff @(posedge clk) begin
    if (reset)
      error <= 0;
    else begin
      assert (din != 4'hF) else
        error <= 1;
    end
  end
endmodule
