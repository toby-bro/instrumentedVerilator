module mod_continuous(input logic [3:0] in, output logic [3:0] out);
  assign out = in + 4'd1;
endmodule
module mod_always_ff(input logic clk, input logic rst, input logic [7:0] d, output logic [7:0] q);
  always_ff @(posedge clk) begin
    if (rst) q <= '0;
    else    q <= d;
  end
endmodule
module mod_always_comb_case(input logic [1:0] sel,
                            input logic [7:0] in0, in1, in2, in3,
                            output logic [7:0] out);
  always_comb begin
    case (sel)
      2'b00: out = in0;
      2'b01: out = in1;
      2'b10: out = in2;
      default: out = in3;
    endcase
  end
endmodule
module mod_generate_loop(input logic [3:0] in,
                         output logic [3:0] out);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      assign out[i] = in[i] & 1'b1;
    end
  endgenerate
endmodule
module mod_parameterized #(parameter WIDTH = 8)
                          (input logic [WIDTH-1:0] a,
                           output logic [WIDTH-1:0] b);
  assign b = a ^ {WIDTH{1'b1}};
endmodule
module mod_struct_union(input logic [15:0] x,
                        output logic [7:0] y);
  typedef struct packed { logic [7:0] a; logic [7:0] b; } mystruct_t;
  union packed { mystruct_t s; logic [15:0] u; } uvar;
  always_comb begin
    uvar.u = x;
    y = uvar.s.a;
  end
endmodule
module mod_enum(input logic clk,
                input logic rst,
                output logic [1:0] state_out);
  typedef enum logic [1:0] { IDLE, BUSY, DONE } state_t;
  state_t state;
  always_ff @(posedge clk) begin
    if (rst) state <= IDLE;
    else begin
      case (state)
        IDLE: state <= BUSY;
        BUSY: state <= DONE;
        default: state <= IDLE;
      endcase
    end
  end
  assign state_out = state;
endmodule
module mod_function(input logic [7:0] a,
                    output logic parity);
  function logic calc_parity(input logic [7:0] v);
    integer i;
    begin
      calc_parity = 1'b0;
      for (i = 0; i < 8; i = i + 1)
        calc_parity = calc_parity ^ v[i];
    end
  endfunction
  assign parity = calc_parity(a);
endmodule
module mod_task(input logic [3:0] a, b,
                output logic [4:0] sum);
  task automatic do_sum(input logic [3:0] x,
                        input logic [3:0] y,
                        output logic [4:0] z);
    begin
      z = x + y;
    end
  endtask
  always_comb begin
    do_sum(a, b, sum);
  end
endmodule
class my_counter;
  int count;
  function new();
    begin
      count = 0;
    end
  endfunction
  function void incr();
    begin
      count++;
    end
  endfunction
endclass
module mod_class(input logic clk,
                 input logic rst,
                 output logic [31:0] count_out);
  my_counter c;
  always_ff @(posedge clk) begin
    if (rst) begin
      c = new();
      count_out <= 0;
    end else begin
      c.incr();
      count_out <= c.count;
    end
  end
endmodule
module mod_generate_if(input logic [3:0] in,
                       output logic [3:0] out);
  parameter USE_IN = 1;
  generate
    if (USE_IN) begin
      assign out = in;
    end else begin
      assign out = 4'b0000;
    end
  endgenerate
endmodule
