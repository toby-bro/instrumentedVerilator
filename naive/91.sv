module comb_logic (input logic a, b, output logic y);
  assign y = (a & b) | ~b;
endmodule
module seq_counter (input logic clk, rst_n, output logic [3:0] count);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) count <= 0;
    else count <= count + 1;
  end
endmodule
module param_adder #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in1, in2, output logic [WIDTH:0] sum);
  assign sum = in1 + in2;
endmodule
module gen_array (input logic [7:0] in, output logic [7:0] out);
  genvar i;
  generate
    for (i = 0; i < 8; i = i + 1) begin : gen_bits
      assign out[i] = in[i] ^ in[(i + 1) % 8];
    end
  endgenerate
endmodule
module struct_mod (input logic clk, rst_n, input logic [7:0] data_in, output logic [7:0] data_out);
  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } nibble_t;
  nibble_t reg_data;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) reg_data <= '0;
    else begin
      reg_data.hi <= data_in[7:4];
      reg_data.lo <= data_in[3:0];
    end
  end
  assign data_out = {reg_data.lo, reg_data.hi};
endmodule
module union_mod (input logic [7:0] in, output logic [15:0] out_high_low);
  typedef union packed {
    logic [15:0] full;
    struct packed { logic [7:0] high; logic [7:0] low; } parts;
  } u16_t;
  u16_t u;
  always_comb begin
    u.parts.high = in;
    u.parts.low  = ~in;
  end
  assign out_high_low = u.full;
endmodule
module pkg_func (input logic [3:0] in, output logic [3:0] out);
  function logic [3:0] reverse_bits(input logic [3:0] val);
    reverse_bits = {val[0], val[1], val[2], val[3]};
  endfunction
  assign out = reverse_bits(in);
endmodule
module class_mod (input logic clk, rst_n, input logic en, output logic done);
  class task_c;
    bit completed;
    function new();
      completed = 0;
    endfunction
    function void run(input bit go);
      if (go) completed = 1;
    endfunction
  endclass
  task_c tc;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tc = new();
      done <= 0;
    end else begin
      tc.run(en);
      done <= tc.completed;
    end
  end
endmodule
