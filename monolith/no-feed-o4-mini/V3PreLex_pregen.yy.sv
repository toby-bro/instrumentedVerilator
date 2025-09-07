module lex_module(input logic clk, input logic rst_n, output logic yylex_done);
  class Lex;
    function void lex(); endfunction
    function new(); endfunction
  endclass
  Lex lex_inst;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lex_inst = new();
      yylex_done <= 0;
    end else begin
      lex_inst.lex();
      yylex_done <= 1;
    end
  end
endmodule
module buffer_module(input logic start_buf, output logic buf_ready);
  class BufferState;
    function void create_buffer(int size); endfunction
    function void delete_buffer(); endfunction
    function new(); endfunction
  endclass
  BufferState bs;
  always_ff @(posedge start_buf) begin
    bs = new();
    bs.create_buffer(16);
    bs.delete_buffer();
    buf_ready <= 1;
  end
endmodule
module state_module(input logic [7:0] ch, input logic [9:0] curr_state, output logic [9:0] next_state);
  localparam int N = 660;
  logic [31:0] base [0:N-1];
  logic [9:0] def_arr [0:N-1];
  logic [7:0] meta [0:56];
  logic [31:0] nxt [0:2172];
  always_comb begin
    int idx;
    logic [7:0] c = ch;
    logic [31:0] b = base[curr_state];
    idx = b + c;
    if (idx < 2173)
      next_state = nxt[idx];
    else
      next_state = def_arr[curr_state];
  end
endmodule
module unput_module(input logic [7:0] inp_c, input logic [15:0] buf_ptr, output logic [15:0] new_ptr);
  always_comb begin
    new_ptr = buf_ptr - 1;
  end
endmodule
module error_module(input logic err, output logic terminate);
  import "DPI-C" function void yy_fatal_error(string msg);
  always_comb begin
    if (err) begin
      yy_fatal_error("fatal flex scanner internal error");
      terminate = 1;
    end else begin
      terminate = 0;
    end
  end
endmodule
module accessors_module(input logic [31:0] line_in, input logic debug_in, output logic [31:0] line_out, output logic debug_out);
  class Acc;
    function int get_lineno(); endfunction
    function void set_lineno(int l); endfunction
    function int get_debug(); endfunction
    function void set_debug(int d); endfunction
    function new(); endfunction
  endclass
  Acc acc;
  always_ff @(posedge line_in[0]) begin
    acc = new();
    acc.set_lineno(line_in);
    acc.set_debug(debug_in);
    line_out <= acc.get_lineno();
    debug_out <= acc.get_debug();
  end
endmodule
module dyn_mem_module(input logic alloc_en, input logic free_en, output logic op_done);
  class Mem;
    function void *alloc(int size); endfunction
    function void free(void *p); endfunction
    function new(); endfunction
  endclass
  Mem m;
  void *p;
  always_ff @(posedge alloc_en) begin
    m = new();
    p = m.alloc(32);
    op_done <= 0;
  end
  always_ff @(posedge free_en) begin
    m.free(p);
    op_done <= 1;
  end
endmodule
module scan_module(input logic [7:0] byte_in, input logic [31:0] len, output logic [31:0] len_out);
  class Scanner;
    function void scan_buffer(ref byte arr[], int size); endfunction
    function void scan_string(string s); endfunction
    function void scan_bytes(ref byte arr[], int size); endfunction
    function new(); endfunction
  endclass
  Scanner sc;
  byte buffer_arr[1024];
  always_ff @(posedge byte_in[0]) begin
    sc = new();
    sc.scan_buffer(buffer_arr, len);
    sc.scan_string("test");
    sc.scan_bytes(buffer_arr, len);
    len_out <= len;
  end
endmodule
module state_stack_module(input logic push, input logic pop, input logic [3:0] state_in, output logic [3:0] state_out);
  logic [3:0] stack [0:31];
  int sp;
  always_ff @(posedge push) begin
    stack[sp] <= state_in;
    sp <= sp + 1;
  end
  always_ff @(posedge pop) begin
    sp <= sp - 1;
    state_out <= stack[sp];
  end
endmodule
