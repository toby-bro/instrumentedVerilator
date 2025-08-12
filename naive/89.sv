module mod_seq (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  in_data,
  output logic [7:0]  out_data
);
  always_ff @(posedge clk) begin
    if (rst)
      out_data <= 8'h00;
    else
      out_data <= in_data;
  end
endmodule
module mod_comb (
  input  logic [1:0]  sel,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  output logic [7:0]  y
);
  always_comb begin
    case (sel)
      2'b00: y = a & b;
      2'b01: y = a | b;
      2'b10: y = a ^ b;
      default: y = a + b;
    endcase
  end
endmodule
module mod_func_task (
  input  logic [3:0]  data_in,
  output logic [3:0]  data_out
);
  function logic [3:0] invert_bits(logic [3:0] in);
    invert_bits = ~in;
  endfunction
  task automatic rotate_left(input  logic [3:0] in, output logic [3:0] out);
    out = {in[2:0], in[3]};
  endtask
  always_comb begin
    logic [3:0] inv;
    inv = invert_bits(data_in);
    rotate_left(inv, data_out);
  end
endmodule
module mod_class_rand (
  input  logic [7:0]  seed,
  input  logic        clk,
  input  logic        rst,
  output logic [7:0]  rnd_out
);
  class RandGen;
    rand logic [7:0] value;
    function new(); endfunction
  endclass
  always_ff @(posedge clk) begin
    if (rst)
      rnd_out <= 8'd0;
    else begin
      RandGen rg;
      rg = new;
      rg.randomize();
      rnd_out <= rg.value ^ seed;
    end
  end
endmodule
module mod_struct_union (
  input  logic [15:0] bus_in,
  output logic [7:0]  low_byte,
  output logic [7:0]  high_byte
);
  typedef struct packed { logic [7:0] low; logic [7:0] high; } bytes_t;
  union packed { bytes_t b; logic [15:0] w; } u;
  always_comb begin
    u.w       = bus_in;
    low_byte  = u.b.low;
    high_byte = u.b.high;
  end
endmodule
module mod_assert (
  input  logic [3:0] x,
  input  logic [3:0] y,
  output logic       z
);
  always_comb begin
    z = (x > y);
    assert (x != y) else z = 1'b0;
  end
endmodule
module mod_cover (
  input  logic [3:0] sig,
  output logic       dup
);
  covergroup cg @(sig);
    coverpoint sig {
      bins low  = {4'd0};
      bins high = {[4'd1:4'd15]};
    }
  endgroup
  cg cg_inst = new();
  always_comb begin
    dup = sig;
    cg_inst.sample();
  end
endmodule
module mod_generate #(
  parameter N = 4
) (
  input  logic [N-1:0] in_vec,
  output logic [N-1:0] out_vec
);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin : gen_loop
      assign out_vec[i] = ~in_vec[i];
    end
  endgenerate
endmodule
