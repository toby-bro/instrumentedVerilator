module mod_lex(input  logic [31:0] in_data, output logic [31:0] out_data);
  class C_lex;
    function logic [31:0] lex_f(input logic [31:0] a);
      lex_f = a + 1;
    endfunction
  endclass
  C_lex obj;
  always_comb begin
    obj = new;
    out_data = obj.lex_f(in_data);
  end
endmodule
module mod_yy_get_next_buffer(input  logic [31:0] in_data, output logic [31:0] out_data);
  class C_gnb;
    function logic [31:0] get_next(input logic [31:0] a);
      get_next = a - 1;
    endfunction
  endclass
  C_gnb obj;
  always_comb begin
    obj = new;
    out_data = obj.get_next(in_data);
  end
endmodule
module mod_yy_get_previous_state(input  logic [31:0] in_data, output logic [31:0] out_data);
  class C_prev;
    function logic [31:0] prev_state(input logic [31:0] a);
      prev_state = a ^ 32'hA5A5A5A5;
    endfunction
  endclass
  C_prev obj;
  always_comb begin
    obj = new;
    out_data = obj.prev_state(in_data);
  end
endmodule
module mod_yy_try_NUL_trans(input  logic [31:0] in_data, output logic [31:0] out_data);
  class C_trynul;
    function logic [31:0] trynul_f(input logic [31:0] a);
      trynul_f = (a == 0) ? 1 : 0;
    endfunction
  endclass
  C_trynul obj;
  always_comb begin
    obj = new;
    out_data = obj.trynul_f(in_data);
  end
endmodule
module mod_yy_unput(input  logic [7:0] ch_in, input logic [31:0] ptr_in, output logic [31:0] out_data);
  class C_unput;
    function logic [31:0] unput_f(input logic [7:0] ch, input logic [31:0] p);
      unput_f = {24'd0, ch} + p;
    endfunction
  endclass
  C_unput obj;
  always_comb begin
    obj = new;
    out_data = obj.unput_f(ch_in, ptr_in);
  end
endmodule
module mod_restart(input  logic [31:0] in_data, output logic [31:0] out_data);
  class C_restart;
    function logic [31:0] restart_f(input logic [31:0] a);
      restart_f = ~a;
    endfunction
  endclass
  C_restart obj;
  always_comb begin
    obj = new;
    out_data = obj.restart_f(in_data);
  end
endmodule
module mod_switch_to_buffer(input  logic [31:0] buf_in, output logic [31:0] out_data);
  class C_switch;
    function logic [31:0] stbuf_f(input logic [31:0] b);
      stbuf_f = b << 1;
    endfunction
  endclass
  C_switch obj;
  always_comb begin
    obj = new;
    out_data = obj.stbuf_f(buf_in);
  end
endmodule
module mod_create_buffer(input  logic [31:0] file_in, input logic [31:0] size_in, output logic [31:0] out_data);
  class C_create;
    function logic [31:0] create_f(input logic [31:0] f, input logic [31:0] s);
      create_f = f + s;
    endfunction
  endclass
  C_create obj;
  always_comb begin
    obj = new;
    out_data = obj.create_f(file_in, size_in);
  end
endmodule
module mod_delete_buffer(input  logic [31:0] buf_in, output logic [31:0] out_data);
  class C_deletebuf;
    function logic [31:0] delbuf_f(input logic [31:0] b);
      delbuf_f = b - 1;
    endfunction
  endclass
  C_deletebuf obj;
  always_comb begin
    obj = new;
    out_data = obj.delbuf_f(buf_in);
  end
endmodule
module mod_init_buffer(input  logic [31:0] buf_in, input logic [31:0] file_in, output logic [31:0] out_data);
  class C_initbuf;
    function logic [31:0] initbuf_f(input logic [31:0] b, input logic [31:0] f);
      initbuf_f = b ^ f;
    endfunction
  endclass
  C_initbuf obj;
  always_comb begin
    obj = new;
    out_data = obj.initbuf_f(buf_in, file_in);
  end
endmodule
module mod_flush_buffer(input  logic [31:0] buf_in, output logic [31:0] out_data);
  class C_flushbuf;
    function logic [31:0] flushbuf_f(input logic [31:0] b);
      flushbuf_f = b;
    endfunction
  endclass
  C_flushbuf obj;
  always_comb begin
    obj = new;
    out_data = obj.flushbuf_f(buf_in);
  end
endmodule
module mod_push_buffer_state(input  logic [31:0] buf_in, output logic [31:0] out_data);
  class C_pushbuf;
    function logic [31:0] pushbuf_f(input logic [31:0] b);
      pushbuf_f = b + 2;
    endfunction
  endclass
  C_pushbuf obj;
  always_comb begin
    obj = new;
    out_data = obj.pushbuf_f(buf_in);
  end
endmodule
module mod_pop_buffer_state(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_popbuf;
    function logic [31:0] popbuf_f(input logic [31:0] d);
      popbuf_f = d;
    endfunction
  endclass
  C_popbuf obj;
  always_comb begin
    obj = new;
    out_data = obj.popbuf_f(dummy);
  end
endmodule
module mod_ensure_buffer_stack(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_ensure;
    function logic [31:0] ensure_f(input logic [31:0] d);
      ensure_f = d ? 1 : 0;
    endfunction
  endclass
  C_ensure obj;
  always_comb begin
    obj = new;
    out_data = obj.ensure_f(dummy);
  end
endmodule
module mod_scan_buffer(input  logic [31:0] base_in, input logic [31:0] size_in, output logic [31:0] out_data);
  class C_scanbuf;
    function logic [31:0] scanbuf_f(input logic [31:0] b, input logic [31:0] s);
      scanbuf_f = b - s;
    endfunction
  endclass
  C_scanbuf obj;
  always_comb begin
    obj = new;
    out_data = obj.scanbuf_f(base_in, size_in);
  end
endmodule
module mod_scan_string(input  logic [31:0] ptr_in, output logic [31:0] out_data);
  class C_scans;
    function logic [31:0] scans_f(input logic [31:0] p);
      scans_f = p;
    endfunction
  endclass
  C_scans obj;
  always_comb begin
    obj = new;
    out_data = obj.scans_f(ptr_in);
  end
endmodule
module mod_scan_bytes(input  logic [31:0] ptr_in, input logic [31:0] len_in, output logic [31:0] out_data);
  class C_scanb;
    function logic [31:0] scanb_f(input logic [31:0] p, input logic [31:0] l);
      scanb_f = p + l;
    endfunction
  endclass
  C_scanb obj;
  always_comb begin
    obj = new;
    out_data = obj.scanb_f(ptr_in, len_in);
  end
endmodule
module mod_yy_push_state(input  logic [31:0] state_in, output logic [31:0] out_data);
  class C_pushs;
    function logic [31:0] pushs_f(input logic [31:0] s);
      pushs_f = s;
    endfunction
  endclass
  C_pushs obj;
  always_comb begin
    obj = new;
    out_data = obj.pushs_f(state_in);
  end
endmodule
module mod_yy_pop_state(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_pops;
    function logic [31:0] pops_f(input logic [31:0] d);
      pops_f = d;
    endfunction
  endclass
  C_pops obj;
  always_comb begin
    obj = new;
    out_data = obj.pops_f(dummy);
  end
endmodule
module mod_yy_fatal_error(input  logic [7:0] msg_in, output logic [31:0] out_data);
  class C_fatal;
    function logic [31:0] fatal_f(input logic [7:0] c);
      fatal_f = c;
    endfunction
  endclass
  C_fatal obj;
  always_comb begin
    obj = new;
    out_data = obj.fatal_f(msg_in);
  end
endmodule
module mod_get_lineno(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_ln;
    function logic [31:0] getln_f(input logic [31:0] d);
      getln_f = d + 10;
    endfunction
  endclass
  C_ln obj;
  always_comb begin
    obj = new;
    out_data = obj.getln_f(dummy);
  end
endmodule
module mod_get_in(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_in;
    function logic [31:0] getin_f(input logic [31:0] d);
      getin_f = d;
    endfunction
  endclass
  C_in obj;
  always_comb begin
    obj = new;
    out_data = obj.getin_f(dummy);
  end
endmodule
module mod_get_out(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_out;
    function logic [31:0] getout_f(input logic [31:0] d);
      getout_f = d;
    endfunction
  endclass
  C_out obj;
  always_comb begin
    obj = new;
    out_data = obj.getout_f(dummy);
  end
endmodule
module mod_get_leng(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_len;
    function logic [31:0] getleng_f(input logic [31:0] d);
      getleng_f = d;
    endfunction
  endclass
  C_len obj;
  always_comb begin
    obj = new;
    out_data = obj.getleng_f(dummy);
  end
endmodule
module mod_get_text(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_text;
    function logic [31:0] gettext_f(input logic [31:0] d);
      gettext_f = d;
    endfunction
  endclass
  C_text obj;
  always_comb begin
    obj = new;
    out_data = obj.gettext_f(dummy);
  end
endmodule
module mod_set_lineno(input  logic [31:0] line_in, output logic [31:0] out_data);
  class C_setln;
    function logic [31:0] setln_f(input logic [31:0] l);
      setln_f = l;
    endfunction
  endclass
  C_setln obj;
  always_comb begin
    obj = new;
    out_data = obj.setln_f(line_in);
  end
endmodule
module mod_set_in(input  logic [31:0] in_stream, output logic [31:0] out_data);
  class C_setin;
    function logic [31:0] setin_f(input logic [31:0] s);
      setin_f = s;
    endfunction
  endclass
  C_setin obj;
  always_comb begin
    obj = new;
    out_data = obj.setin_f(in_stream);
  end
endmodule
module mod_set_out(input  logic [31:0] out_stream, output logic [31:0] out_data);
  class C_setout;
    function logic [31:0] setout_f(input logic [31:0] s);
      setout_f = s;
    endfunction
  endclass
  C_setout obj;
  always_comb begin
    obj = new;
    out_data = obj.setout_f(out_stream);
  end
endmodule
module mod_get_debug(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_gdbg;
    function logic [31:0] getdbg_f(input logic [31:0] d);
      getdbg_f = d & 1;
    endfunction
  endclass
  C_gdbg obj;
  always_comb begin
    obj = new;
    out_data = obj.getdbg_f(dummy);
  end
endmodule
module mod_set_debug(input  logic [31:0] dbg_flag, output logic [31:0] out_data);
  class C_sdbg;
    function logic [31:0] setdbg_f(input logic [31:0] f);
      setdbg_f = f;
    endfunction
  endclass
  C_sdbg obj;
  always_comb begin
    obj = new;
    out_data = obj.setdbg_f(dbg_flag);
  end
endmodule
module mod_lex_destroy(input  logic [31:0] dummy, output logic [31:0] out_data);
  class C_lexdestroy;
    function logic [31:0] lexdestroy_f(input logic [31:0] d);
      lexdestroy_f = d;
    endfunction
  endclass
  C_lexdestroy obj;
  always_comb begin
    obj = new;
    out_data = obj.lexdestroy_f(dummy);
  end
endmodule
module mod_alloc(input  logic [31:0] size_in, output logic [31:0] out_data);
  class C_alloc;
    function logic [31:0] alloc_f(input logic [31:0] s);
      alloc_f = s;
    endfunction
  endclass
  C_alloc obj;
  always_comb begin
    obj = new;
    out_data = obj.alloc_f(size_in);
  end
endmodule
module mod_realloc(input  logic [31:0] ptr_in, input logic [31:0] size_in, output logic [31:0] out_data);
  class C_realloc;
    function logic [31:0] realloc_f(input logic [31:0] p, input logic [31:0] s);
      realloc_f = p + s;
    endfunction
  endclass
  C_realloc obj;
  always_comb begin
    obj = new;
    out_data = obj.realloc_f(ptr_in, size_in);
  end
endmodule
module mod_free(input  logic [31:0] ptr_in, output logic [31:0] out_data);
  class C_free;
    function logic [31:0] free_f(input logic [31:0] p);
      free_f = p;
    endfunction
  endclass
  C_free obj;
  always_comb begin
    obj = new;
    out_data = obj.free_f(ptr_in);
  end
endmodule
