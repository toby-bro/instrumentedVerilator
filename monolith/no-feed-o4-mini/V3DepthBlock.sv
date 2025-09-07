module deep_expr(input  logic [7:0] a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, output logic [7:0] z);
  assign z = (((((((((((((a + b) - c) * d) / e) % f) & g) | h) ^ i) << j) >> k) ? l : m) + n) - o) + p) - q + (r * s) - t;
endmodule
module use_function(input  logic [3:0] x, y, output logic [3:0] z);
  function automatic logic [3:0] deep_func(input logic [3:0] u, v);
    logic [3:0] tmp1, tmp2, tmp3;
    tmp1 = u ^ v;
    tmp2 = u & v;
    tmp3 = u | v;
    return tmp1 + tmp2 - tmp3;
  endfunction
  assign z = deep_func(x, y);
endmodule
module use_loop(input  logic        clk, reset, input logic [7:0] in, output logic [7:0] out);
  integer i;
  always_ff @(posedge clk) begin
    if (!reset) begin
      out <= '0;
    end else begin
      out <= '0;
      for (i = 0; i < 8; i = i + 1) begin
        if (in[i]) begin
          out[i] <= 1;
          break;
        end
      end
      while (in != 0) begin
        if (in == out) begin
          continue;
        end
        break;
      end
    end
  end
endmodule
module use_ifcase(input  logic [1:0] sel, input logic [7:0] din, output logic [7:0] dout);
  always_comb begin
    if (sel == 2'b00) dout = din + 1;
    else if (sel == 2'b01) dout = din - 1;
    else begin
      case (sel)
        2'b10: dout = din & 8'hF0;
        default: dout = din | 8'h0F;
      endcase
    end
  end
endmodule
module use_task(input  logic        clk, start, output logic done);
  task automatic gen_task(output logic flag);
    logic [3:0] tmp;
    tmp = 0;
    repeat (5) begin
      tmp = tmp + 1;
    end
    flag = (tmp == 5);
  endtask
  always_ff @(posedge clk) begin
    if (start) begin
      gen_task(done);
    end
  end
endmodule
module use_struct(input  logic [7:0] a, b, output logic [7:0] sum);
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } half_t;
  half_t x, y;
  assign x = {a[7:4], a[3:0]};
  assign y = {b[7:4], b[3:0]};
  assign sum = {4'b0000, x.lo} + {4'b0000, y.lo};
endmodule
module use_union(input  logic [7:0] in, output logic [7:0] out, output logic [7:0] direct);
  typedef union packed { logic [7:0] u8; logic [1:0] bits [3:0]; } utype;
  utype u;
  always_comb begin
    u.u8 = in;
    out    = u.u8;
    direct = {u.bits[0], u.bits[1], u.bits[2], u.bits[3]};
  end
endmodule
interface my_intf(input logic clk);
  logic req;
  logic ack;
  modport sm(input clk, req, output ack);
endinterface
module use_intf(my_intf.sm i, output logic done);
  always_ff @(posedge i.clk) begin
    if (i.req) done <= 1;
    else        done <= 0;
  end
endmodule
module use_generate(input  logic [3:0] in, output logic [3:0] out);
  genvar gv;
  generate
    for (gv = 0; gv < 4; gv = gv + 1) begin : gen_loop
      assign out[gv] = in[gv];
    end
  endgenerate
endmodule
module use_enum(input  logic [1:0] sel, output logic [7:0] out);
  typedef enum logic [1:0] { STATE_IDLE, STATE_RUN, STATE_DONE, STATE_ERR } state_t;
  state_t st;
  always_comb begin
    case (sel)
      STATE_IDLE: st = STATE_RUN;
      STATE_RUN : st = STATE_DONE;
      STATE_DONE: st = STATE_IDLE;
      default   : st = STATE_ERR;
    endcase
    out = {6'b0, st};
  end
endmodule
