module m_unary(input logic [7:0] a, output logic [7:0] out_not, output logic and_reduce, output logic or_reduce, output logic xor_reduce);
  assign out_not     = ~a;
  assign and_reduce  = &a;
  assign or_reduce   = |a;
  assign xor_reduce  = ^a;
endmodule
module m_binary(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum, output logic [7:0] diff, output logic [15:0] prod, output logic [7:0] band, output logic [7:0] bor, output logic [7:0] bxor, output logic [7:0] lshift, output logic [7:0] rshift);
  assign sum    = a + b;
  assign diff   = a - b;
  assign prod   = a * b;
  assign band   = a & b;
  assign bor    = a | b;
  assign bxor   = a ^ b;
  assign lshift = a << b[2:0];
  assign rshift = a >> b[2:0];
endmodule
module m_conditional(input logic sel, input logic [3:0] a, input logic [3:0] b, output logic [3:0] y);
  assign y = sel ? a : b;
endmodule
module m_nested_conditional(input logic [1:0] sel, input logic [7:0] a, input logic [7:0] b, input logic [7:0] c, output logic [7:0] y);
  assign y = (sel == 2'd0) ? a :
             (sel == 2'd1) ? b : c;
endmodule
module m_concat(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic [3:0] d, output logic [15:0] y);
  assign y = {a, b, c, d};
endmodule
module m_pack_unpack(input logic [7:0] a, output logic [1:0] p0, output logic [3:0] p1, output logic [3:0] p2);
  assign p0 = a[1:0];
  assign p1 = a[7:4];
  assign p2 = a[3:0];
endmodule
module m_part_select_dynamic(input logic [7:0] a, input logic [2:0] idx, output logic [3:0] y_inc, output logic [3:0] y_dec);
  assign y_inc = a[idx +: 4];
  assign y_dec = a[idx -: 4];
endmodule
module m_array(input logic [7:0] arr_in [0:3], output logic [7:0] arr_out [0:3], input logic [1:0] index, output logic [7:0] sel);
  assign arr_out = arr_in;
  assign sel     = arr_in[index];
endmodule
module m_struct(input logic [3:0] a, input logic [3:0] b, output logic [7:0] y);
  typedef struct packed { logic [3:0] f0; logic [3:0] f1; } my_struct_t;
  my_struct_t s;
  assign s.f0 = a;
  assign s.f1 = b;
  assign y    = s;
endmodule
module m_generate(input logic [3:0] a, output logic [3:0] y [0:3]);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      assign y[i] = a + i;
    end
  endgenerate
endmodule
module m_generate_if(input logic [3:0] a, input logic en, output logic [3:0] y);
  always_comb begin
    if (en) y = a + 4;
    else   y = a - 4;
  end
endmodule
module m_case(input logic [1:0] sel, input logic [7:0] a, input logic [7:0] b, input logic [7:0] c, output logic [7:0] y);
  always_comb begin
    case (sel)
      2'd0: y = a;
      2'd1: y = b;
      default: y = c;
    endcase
  end
endmodule
module m_while(input logic clk, input logic rst, input logic [3:0] init, output logic [7:0] count);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) count <= init;
    else begin
      integer i;
      i = 0;
      while (i < 4) begin
        count <= count + i;
        i = i + 1;
      end
    end
  end
endmodule
module m_do(input logic clk, input logic rst, output logic [3:0] d);
  always_ff @(posedge clk or posedge rst) begin
    if (rst) d <= 4'd0;
    else begin
      integer i;
      i = 0;
      do begin
        d <= d + 1;
        i = i + 1;
      end while (i < 2);
    end
  end
endmodule
module m_class(input logic clk, input logic rst, input logic [7:0] a, output logic [7:0] y);
  class MyClass;
    function new(); endfunction
    function logic [7:0] f(input logic [7:0] v); return v + 8'h1; endfunction
  endclass
  always_ff @(posedge clk or posedge rst) begin
    if (rst) y <= 8'h00;
    else begin
      MyClass c;
      c = new();
      y <= c.f(a);
    end
  end
endmodule
module m_func_call(input logic [7:0] a, input logic [7:0] b, output logic [31:0] y_clog2);
  assign y_clog2 = $clog2(a + b);
endmodule
module m_task_call(input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
  function automatic logic [7:0] sum_func(input logic [7:0] x, input logic [7:0] z);
    return x + z;
  endfunction
  assign y = sum_func(a, b);
endmodule
interface m_intf();
  logic sig;
endinterface
module m_interface_user(input logic in_sig, output logic out_sig);
  m_intf intf_if();
  assign intf_if.sig = in_sig;
  assign out_sig      = intf_if.sig;
endmodule
