module var_pipe(input  logic        clk,
                input  logic        rst,
                input  logic [7:0]  in,
                output logic [7:0]  out);
  always_ff @(posedge clk) begin
    if (rst) out <= 0;
    else     out <= in;
  end
endmodule
module class_mod(input  logic        clk,
                 input  logic        rst,
                 input  logic [7:0]  din,
                 output logic [7:0]  dout);
  class pkt;
    rand logic [7:0] data;
    function new(); endfunction
  endclass
  pkt p;
  always_ff @(posedge clk) begin
    if (rst) begin
      p = new();
      dout <= 0;
    end else begin
      p = new();
      p.data = din;
      dout <= p.data;
    end
  end
endmodule
module struct_union(input  logic [3:0] a,
                    input  logic [3:0] b,
                    output logic [4:0] sum,
                    output logic       lsb);
  typedef struct packed { logic [3:0] x; logic [3:0] y; } my_s;
  typedef union  packed { logic [7:0] u; my_s s; } my_u;
  my_u u_inst;
  always_comb begin
    u_inst.s.x = a;
    u_inst.s.y = b;
    sum = u_inst.s.x + u_inst.s.y;
    lsb = u_inst.u[0];
  end
endmodule
module enum_mod(input  logic [1:0] sel,
                output logic [7:0] out);
  typedef enum logic [1:0] {IDLE=2'b00, BUSY=2'b01, DONE=2'b10} state_t;
  state_t st;
  always_comb begin
    st = state_t'(sel);
    case (st)
      IDLE: out = 8'h11;
      BUSY: out = 8'h22;
      DONE: out = 8'h33;
      default: out = 8'hFF;
    endcase
  end
endmodule
module generate_mod
  #(parameter N = 4)
  (input  logic        clk,
   input  logic        rst,
   input  logic        in,
   output logic [N-1:0] outs);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_blk
      always_ff @(posedge clk) begin
        if (rst) outs[i] <= 0;
        else     outs[i] <= in;
      end
    end
  endgenerate
endmodule
module interface_mod(input  logic in,
                     output logic out);
  interface simple_if(input logic sig_in, output logic sig_out);
    logic mid;
    modport um (input mid, output sig_out);
  endinterface
  simple_if intf(.sig_in(in), .sig_out(out));
  always_comb begin
    intf.mid = intf.sig_in;
    intf.sig_out = intf.mid;
  end
endmodule
module func_task_mod(input  logic [3:0] a,
                     input  logic [3:0] b,
                     output logic [4:0] res,
                     output logic       ok);
  function automatic logic [4:0] do_add(input logic [3:0] x, input logic [3:0] y);
    do_add = x + y;
  endfunction
  task automatic do_check(input logic [4:0] v, output logic f);
    f = (v > 9);
  endtask
  always_comb begin
    res = do_add(a, b);
    do_check(res, ok);
  end
endmodule
module param_mod
  #(parameter WIDTH = 8,
    parameter DEPTH = 1)
  (input  logic [WIDTH-1:0] in,
   output logic [7:0]       out);
  localparam LOG2DEPTH = $clog2(DEPTH);
  always_comb begin
    out = in[LOG2DEPTH +: 8];
  end
endmodule
