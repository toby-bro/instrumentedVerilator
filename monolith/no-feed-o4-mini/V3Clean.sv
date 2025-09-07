module debug_mod(input logic enable, output logic [3:0] level_out);
  localparam int DLEVEL = 1;
  function automatic int debug; input int lvl; return lvl + DLEVEL; endfunction
  assign level_out = debug(enable);
endmodule
module dump_tree_level_mod(input logic [1:0] mode, output logic [31:0] out1);
  function automatic int dump_tree_level; input int lvl; case(lvl) 2'b00: return 0; 2'b01: return 1; default: return -1; endcase endfunction
  assign out1 = dump_tree_level(mode);
endmodule
module dump_tree_json_level_mod(input logic [3:0] j, output logic [31:0] out2);
  function automatic int dump_tree_json_level; input int lvl; input int flags; return lvl ^ flags; endfunction
  assign out2 = dump_tree_json_level(j, j);
endmodule
module dump_tree_either_level_mod(input logic flag, input logic [3:0] lvl, output logic [31:0] out3);
  function automatic int dump_tree_level; input int l; return l + 10; endfunction
  function automatic int dump_tree_json_level; input int l; input int f; return l - f; endfunction
  function automatic int dump_tree_either_level; input int f; input int l; if (f) return dump_tree_level(l); else return dump_tree_json_level(l, f); endfunction
  assign out3 = dump_tree_either_level(flag, lvl);
endmodule
module set_cpp_width_mod(input logic [2:0] widthMin, output logic [7:0] outWidth);
  function automatic logic [7:0] cpp_width; input logic [2:0] w; if (w <= 3'd4) return 8'd4; else if (w <= 3'd7) return 8'd8; else return w * 2; endfunction
  assign outWidth = cpp_width(widthMin);
endmodule
module compute_cpp_width_mod(input logic do_resize, input logic has_dtype, input logic [2:0] w, output logic [7:0] outW);
  function automatic logic [7:0] compute_cpp_width; input logic [2:0] ww; if (do_resize && has_dtype) begin if (ww <= 3'd4) return 8'd4; else if (ww <= 3'd7) return 8'd8; else return ww * 2; end else return ww; endfunction
  assign outW = compute_cpp_width(w);
endmodule
module is_clean_mod(input logic unknown, input logic clean, output logic result);
  function automatic logic is_clean; input logic u; input logic c; if (u) return c; else return 1'b0; endfunction
  assign result = is_clean(unknown, clean);
endmodule
module set_clean_mod(input logic dirty, input logic wholeUint, output logic [1:0] clean_state);
  typedef enum logic [1:0]{CS_UNKNOWN, CS_CLEAN, CS_DIRTY} clean_t;
  function automatic clean_t set_clean_fn; input logic d; input logic w; if (d || w) return CS_CLEAN; else return CS_DIRTY; endfunction
  assign clean_state = set_clean_fn(dirty, wholeUint);
endmodule
module insert_clean_mod(input logic [7:0] mask_in, input logic [7:0] data_in, output logic [7:0] out);
  function automatic logic [7:0] apply_mask; input logic [7:0] m; input logic [7:0] d; return m & d; endfunction
  assign out = apply_mask(mask_in, data_in);
endmodule
module ensure_clean_mod(input logic [7:0] data_in, input logic clean_flag, output logic [7:0] out);
  always_comb begin if (!clean_flag) out = data_in & 8'hFF; else out = data_in; end
endmodule
module ensure_clean_and_next_mod(input logic [7:0] data_arr [0:3], input logic clean_arr [0:3], output logic [7:0] out_arr [0:3]);
  genvar i;
  generate for (i = 0; i < 4; i = i + 1) begin : gen_clean
    assign out_arr[i] = clean_arr[i] ? data_arr[i] : (data_arr[i] & 8'hFF);
  end endgenerate
endmodule
module operand_biop_mod(input logic [3:0] lhs, input logic [3:0] rhs, input logic clean_lhs, input logic clean_rhs, output logic [3:0] out);
  function automatic logic [3:0] compute_op; input logic [3:0] a; input logic [3:0] b; return a + b; endfunction
  always_comb begin
    logic [3:0] tmp_l = clean_lhs ? lhs : (lhs & 4'hF);
    logic [3:0] tmp_r = clean_rhs ? rhs : (rhs & 4'hF);
    out = compute_op(tmp_l, tmp_r);
  end
endmodule
module operand_triop_mod(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic cl, input logic cr, input logic ct, output logic [3:0] out);
  always_comb out = (cl ? a : a & 4'hF) ^ (cr ? b : b & 4'hF) ^ (ct ? c : c & 4'hF);
endmodule
module operand_quadop_mod(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic [3:0] d, input logic cl, input logic cr, input logic ct, input logic cf, output logic [3:0] out);
  always_comb out = ((cl ? a : a & 4'hF) & (cr ? b : b & 4'hF)) | ((ct ? c : c & 4'hF) ^ (cf ? d : d & 4'hF));
endmodule
module visit_module(input logic [3:0] in1, input logic en, output logic [3:0] out);
  function automatic logic [3:0] visitor; input logic [3:0] x; if (en) return x + 1; else return x - 1; endfunction
  assign out = visitor(in1);
endmodule
module visit_uniop_mod(input logic [3:0] in1, input logic clean_lhs, output logic [3:0] out);
  function automatic logic [3:0] uniop; input logic [3:0] x; return ~x; endfunction
  assign out = clean_lhs ? uniop(in1) : in1;
endmodule
module visit_biop_mod(input logic [3:0] a, input logic [3:0] b, input logic clean_out, output logic [3:0] out);
  always_comb begin out = a + b; if (!clean_out) out = out & 4'hF; end
endmodule
module visit_and_mod(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out);
  assign out = a & b;
endmodule
module visit_xor_mod(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out);
  assign out = a ^ b;
endmodule
module visit_or_mod(input logic [3:0] a, input logic [3:0] b, output logic [3:0] out);
  assign out = a | b;
endmodule
module visit_quadop_mod(input logic [3:0] a, input logic [3:0] b, input logic [3:0] c, input logic [3:0] d, output logic [3:0] out);
  assign out = ((a & b) ^ (c | d));
endmodule
module visit_expr_stmt_mod(input logic [3:0] expr, output logic done);
  assign done = &expr;
endmodule
module visit_node_expr_mod(input logic [3:0] expr, output logic [3:0] out);
  assign out = expr;
endmodule
module visit_node_assign_mod(input logic [3:0] src, output logic [3:0] dst);
  assign dst = src;
endmodule
module visit_ast_text_mod(input logic go, output logic done);
  assign done = go;
endmodule
module visit_ast_scope_name_mod(input logic [7:0] name_code, output logic [7:0] out);
  assign out = name_code;
endmodule
class CNew;
  int val;
  function new(int v); val = v; endfunction
  function int get(); return val; endfunction
endclass
module visit_ast_cnew_mod(input logic [7:0] v_in, output logic [7:0] v_out);
  logic [7:0] tmp;
  CNew new_inst;
  always_comb begin
    new_inst = new(v_in);
    tmp = new_inst.get();
  end
  assign v_out = tmp;
endmodule
module visit_cons_pack_member_mod(input logic [7:0] in_val, input logic [1:0] idx, output logic out);
  logic [7:0] arr [0:3];
  assign arr[0] = 8'hA0; assign arr[1] = 8'hB1; assign arr[2] = 8'hC2; assign arr[3] = 8'hD3;
  assign out = arr[idx][0];
endmodule
module visit_sel_mod(input logic [7:0] data, input logic [2:0] sel, output logic bit_out);
  assign bit_out = data[sel];
endmodule
module visit_ucfunc_mod(input logic [7:0] data0, input logic [7:0] data1, input logic [3:0] idx, output logic [7:0] out);
  function automatic logic [7:0] ucfunc; input logic [7:0] v; return v * 2; endfunction
  always_comb out = ucfunc(data0) & ucfunc(data1);
endmodule
module visit_trace_decl_mod(input logic [3:0] data, output logic [3:0] out);
  assign out = data;
endmodule
module visit_trace_inc_mod(input logic [3:0] value_arr [0:1], output logic [3:0] out);
  assign out = value_arr[0] + value_arr[1];
endmodule
typedef struct packed { logic [3:0] a; logic [3:0] b; } my_struct_t;
module visit_typedef_mod(input my_struct_t in_s, output logic [3:0] out);
  assign out = in_s.a + in_s.b;
endmodule
module visit_paramtype_dtype_mod #(parameter WIDTH = 8) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
  assign out = in;
endmodule
module visit_cond_mod(input logic cond, input logic [3:0] then_val, input logic [3:0] else_val, output logic [3:0] out);
  assign out = cond ? then_val : else_val;
endmodule
module visit_while_mod(input logic [7:0] start, output logic [7:0] count);
  logic [7:0] temp;
  always_comb begin
    temp = start;
    while (temp > 0) temp = temp - 1;
  end
  assign count = temp;
endmodule
module visit_node_if_mod(input logic cond, input logic [3:0] v_then, input logic [3:0] v_else, output logic [3:0] out);
  always_comb if (cond) out = v_then; else out = v_else;
endmodule
module visit_sformatf_mod(input logic [15:0] num, output logic [7:0] str_arr [0:3]);
  genvar i;
  generate for (i = 0; i < 4; i = i + 1) assign str_arr[i] = num[8*i +:8]; endgenerate
endmodule
module visit_ucstmt_mod(input logic [3:0] exprs [0:3], input logic [3:0] flag_arr [0:3], output logic [3:0] out_exprs [0:3]);
  genvar i;
  generate for (i = 0; i < 4; i = i + 1) assign out_exprs[i] = flag_arr[i] ? exprs[i] : (exprs[i] & 4'hF); endgenerate
endmodule
module visit_nodeccall_mod(input logic [3:0] args [0:2], output logic [3:0] result);
  assign result = args[0] + args[1] + args[2];
endmodule
module visit_cmethodhard_mod(input logic [3:0] pins [0:1], output logic hard_out);
  assign hard_out = pins[0] & pins[1];
endmodule
module visit_with_mod(input logic [3:0] in_val, input logic [3:0] param, output logic [3:0] out);
  assign out = in_val + param;
endmodule
module visit_creturn_mod(input logic [3:0] lhs, output logic [3:0] ret_val);
  assign ret_val = lhs;
endmodule
interface my_intf(input logic clk);
  logic [3:0] data;
endinterface
module visit_intfref_mod(my_intf intf, output logic [3:0] out);
  assign out = intf.data;
endmodule
module visit_default_mod(input logic [3:0] in, output logic [3:0] sum);
  assign sum = in + in;
endmodule
module cleanvisitor_mod(input logic [3:0] in, output logic [3:0] out);
  function automatic logic [3:0] cleanvisitor_fn; input logic [3:0] x; return x; endfunction
  assign out = cleanvisitor_fn(in);
endmodule
module v3clean_cleanall_mod(input logic [3:0] in, output logic [3:0] out);
  assign out = in;
endmodule
