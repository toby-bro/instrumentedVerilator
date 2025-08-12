module comb_adder(input  logic [3:0] a, b,
                  output logic [3:0] y);
  class CComb;
    function logic [3:0] sum(input logic [3:0] x, y);
      sum = x + y;
    endfunction
  endclass
  always_comb begin
    CComb comb;
    comb = new();
    y = comb.sum(a, b);
  end
endmodule
module seq_reg(input  logic        clk,
               input  logic        reset_n,
               input  logic [7:0]  in,
               output logic [7:0]  out);
  class CReg;
    function logic [7:0] inc(input logic [7:0] v);
      inc = v + 1;
    endfunction
  endclass
  always_ff @(posedge clk or negedge reset_n) begin
    CReg r;
    if (!reset_n)
      out <= '0;
    else begin
      r = new();
      out <= r.inc(in);
    end
  end
endmodule
module gen_xor
  #(
    parameter int N = 4
  )
  (
    input  logic [N-1:0] a, b,
    output logic [N-1:0] y
  );
  class CGen;
    function logic xor_fn(input logic x, y);
      xor_fn = x ^ y;
    endfunction
  endclass
  always_comb begin
    CGen g;
    g = new();
    for (int i = 0; i < N; i = i + 1)
      y[i] = g.xor_fn(a[i], b[i]);
  end
endmodule
module array_sum(input  logic [7:0] arr [2:0],
                 output logic [15:0] sum);
  class Carr;
    function logic [15:0] sum_array(input logic [7:0] ar [2:0]);
      logic [15:0] s;
      s = 0;
      for (int i = 0; i < 3; i = i + 1)
        s += ar[i];
      return s;
    endfunction
  endclass
  always_comb begin
    Carr arrC;
    arrC = new();
    sum = arrC.sum_array(arr);
  end
endmodule
module struct_enum(input  logic [1:0] sel,
                   output logic [3:0] out);
  typedef struct { logic en; logic [3:0] data; } packet_t;
  typedef enum logic [1:0] { IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10 } state_t;
  state_t   state;
  packet_t  pkt;
  class CStruct;
    function void process(input logic [1:0] s,
                          output state_t       st,
                          inout  packet_t      p,
                          output logic [3:0]   d);
      st      = state_t'(s);
      p.en    = (s == IDLE);
      p.data  = s * 2;
      d       = p.en ? p.data : 4'h0;
    endfunction
  endclass
  always_comb begin
    CStruct cs;
    cs = new();
    cs.process(sel, state, pkt, out);
  end
endmodule
module func_count(input  logic [15:0] in,
                  output logic [4:0]  out);
  function logic [4:0] bitcount(input logic [15:0] v);
    int count;
    count = 0;
    for (int i = 0; i < 16; i = i + 1)
      if (v[i])
        count++;
    return count;
  endfunction
  always_comb begin
    out = bitcount(in);
  end
endmodule
