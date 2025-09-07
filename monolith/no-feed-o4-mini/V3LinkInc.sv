module m_simple_if(input  logic in, output logic out);
  always_comb begin : blk
    if (in) out = 1;
    else     out = 0;
  end
endmodule
module m_case(input  logic [1:0] sel, output logic out);
  always_comb begin
    case (sel)
      2'b00: out = 0;
      2'b01: out = 1;
      default: out = sel[0];
    endcase
  end
endmodule
module m_logical(input  logic a, input logic b, output logic out);
  assign out = ((a && b) || (a == b)) ? 1'b1 : 1'b0;
endmodule
module m_while(input  logic        clk,
               input  logic        rst,
               input  logic [3:0]  in,
               output logic [3:0]  out);
  logic [3:0] cnt;
  always_ff @(posedge clk) begin
    if (rst) begin
      cnt <= 0;
    end else begin
      cnt <= in;
      while (cnt < 4) begin
        cnt <= cnt + 1;
      end
      out <= cnt;
    end
  end
endmodule
module m_foreach(input  logic        clk,
                 input  logic [3:0]  in,
                 output logic [3:0]  out);
  logic [3:0] arr [0:3];
  integer     j;
  always_ff @(posedge clk) begin
    arr[0] <= in;
    foreach (arr[j]) begin
      arr[j] <= arr[j] + 1;
    end
    out <= arr[0];
  end
endmodule
module m_event_wait(input  logic clk,
                    input  logic in,
                    output logic out);
  always_ff @(posedge clk) begin
    wait (in) begin
      out <= 1;
    end
  end
endmodule
module m_generate(input  logic [1:0] in, output logic [1:0] out);
  genvar i;
  generate
    for (i = 0; i < 2; i = i + 1) begin : genblk
      assign out[i] = in[i];
    end
  endgenerate
endmodule
module m_prepost(input  logic        clk,
                 input  logic [3:0]  in,
                 output logic [3:0]  out);
  logic [3:0] a, b;
  always_ff @(posedge clk) begin
    a <= in;
    b <= in;
    a++;    
    ++b;    
    out <= a + b;
  end
endmodule
module m_property(input  logic clk,
                  input  logic reset,
                  input  logic in,
                  output logic out);
  property p_valid;
    @(posedge clk) disable iff (reset) in |-> out;
  endproperty
  assert property (p_valid);
endmodule
module m_task_jump(input  logic        clk,
                   input  logic        in,
                   output logic        out);
  logic tmp;
  function logic foo(input logic a);
    if (a) begin
      foo = 1;
      return;
    end
    foo = 0;
  endfunction
  task mytask(input logic a);
    begin
      tmp = foo(a);
    end
  endtask
  always_ff @(posedge clk) begin
    mytask(in);
    out <= tmp;
  end
endmodule
