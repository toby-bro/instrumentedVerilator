class MyClass;
  int field;
  function new();
    field = 42;
  endfunction
  function void delete();
  endfunction
endclass
module mod_yywrap(input logic enable, output logic wrapped);
  always_comb begin
    wrapped = enable;
  end
endmodule
module mod_yylex(input logic [7:0] data_in, output logic [7:0] token_out);
  int i;
  always_comb begin
    token_out = 0;
    for (i = 0; i < 8; i = i + 1) token_out ^= (data_in >> i);
  end
endmodule
module mod_ctor_inst(input logic clk, output logic [31:0] val_out);
  MyClass obj;
  always_ff @(posedge clk) begin
    obj = new();
    val_out <= obj.field;
  end
endmodule
module mod_delete_inst(input logic clk, output logic ok_out);
  MyClass a;
  always_ff @(posedge clk) begin
    a = new();
    a.delete();
    ok_out <= 1;
  end
endmodule
module mod_switch_streams(input logic [7:0] a, input logic [7:0] b, output logic [7:0] max_out);
  always_comb max_out = (a > b ? a : b);
endmodule
module mod_lex_input(input logic clk, output logic done_out);
  int c;
  always_ff @(posedge clk) begin
    done_out <= 0;
    for (c = 0; c < 10; c = c + 1) done_out <= (c == 9);
  end
endmodule
module mod_lex_output(input logic [7:0] data, output logic nonzero);
  always_comb nonzero = (data != 0);
endmodule
module mod_get_next_buffer(input logic [15:0] buf_array [10:0], output logic [15:0] max_val);
  int i;
  always_comb begin
    max_val = buf_array[0];
    for (i = 1; i < 11; i = i + 1)
      if (buf_array[i] > max_val) max_val = buf_array[i];
  end
endmodule
module mod_get_previous_state(input logic [7:0] state_in, output logic [7:0] prev_state);
  always_comb prev_state = (state_in > 0 ? state_in - 1 : 0);
endmodule
module mod_try_nul_trans(input logic [7:0] state_in, output logic ok_flag);
  always_comb ok_flag = (state_in != 8'd0);
endmodule
module mod_unput(input logic [7:0] in_char, output logic [7:0] out_char);
  always_comb out_char = in_char;
endmodule
module mod_restart(input logic rst, output logic restarted);
  always_ff @(posedge rst) restarted <= 1;
endmodule
module mod_delete_buffer(input logic trigger, output logic done_flag);
  always_ff @(posedge trigger) done_flag <= trigger;
endmodule
module mod_init_buffer(input logic [7:0] data_array [255:0], output logic init_done);
  always_comb init_done = data_array[0];
endmodule
module mod_flush_buffer(input logic [7:0] data_in, output logic flushed);
  int i;
  always_comb begin
    flushed = 0;
    for (i = 0; i < 8; i = i + 1) flushed = flushed | data_in[i%8];
  end
endmodule
module mod_push_buffer_state(input logic push, input logic [7:0] new_buf, output logic [7:0] top_buf);
  logic [7:0] stack [0:3];
  int sp;
  always_ff @(posedge push) begin
    if (sp < 3) sp <= sp + 1;
    stack[sp] <= new_buf;
    top_buf <= stack[sp];
  end
endmodule
module mod_pop_buffer_state(input logic pop, output logic [7:0] top_buf);
  logic [7:0] stack [0:3];
  int sp;
  always_ff @(posedge pop) begin
    if (sp > 0) sp <= sp - 1;
    top_buf <= stack[sp];
  end
endmodule
module mod_ensure_buffer_stack(input logic clk, output logic allocated);
  logic [3:0] stack_arr [0:3];
  int i;
  always_ff @(posedge clk) begin
    for (i = 0; i < 4; i = i + 1) stack_arr[i] <= i;
    allocated <= 1;
  end
endmodule
module mod_push_state(input logic [3:0] state_in, output logic [3:0] cur_state);
  logic [3:0] stack_arr [0:3];
  int sp;
  always_comb begin
    stack_arr[sp] = state_in;
    cur_state = state_in;
  end
endmodule
module mod_pop_state(input logic clk, output logic [3:0] state_out);
  logic [3:0] stack_arr [0:3];
  int sp;
  always_ff @(posedge clk) begin
    if (sp > 0) sp <= sp - 1;
    state_out <= stack_arr[sp];
  end
endmodule
module mod_top_state(input logic [3:0] stack_in, output logic [3:0] top_state);
  always_comb top_state = stack_in;
endmodule
module mod_error(input logic err_in, output logic fatal_out);
  always_comb fatal_out = err_in;
endmodule
module mod_alloc(input logic [31:0] size_in, output logic [31:0] addr_out);
  always_comb addr_out = size_in;
endmodule
module mod_realloc(input logic [31:0] ptr_in, input logic [31:0] size_in, output logic [31:0] new_ptr);
  always_comb new_ptr = ptr_in + size_in;
endmodule
module mod_free(input logic [31:0] ptr_in, output logic freed_out);
  always_comb freed_out = (ptr_in != 0);
endmodule
