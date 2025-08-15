typedef class my_fwd_class;
interface my_fwd_interface;
  logic dummy_if_var;
endinterface
class BaseClass;
  int base_var = 1;
  function void base_method();
    base_var = base_var + 1;
  endfunction
endclass
class DerivedClass extends BaseClass;
  int derived_var = 2;
  function void derived_method();
    derived_var = derived_var + 1;
  endfunction
endclass
class my_class;
  int class_mem;
  function new(int val);
    class_mem = val;
  endfunction
  function void class_task(input int i);
    this.class_mem = i;
  endfunction
endclass
package my_package;
  parameter PKG_PARAM = 100;
  typedef logic [7:0] pkg_byte_t;
endpackage
interface my_interface;
  logic clk_if;
  logic reset_if;
  logic [15:0] data_if;
  function void interface_func_2(input int val_in, output int val_out);
    val_out = val_in + 1;
  endfunction
  modport master_mp (
    output clk_if,
    output reset_if,
    input data_if,
    interface_func_2
  );
  function void interface_func();
    data_if = 16'hAAAA;
  endfunction
endinterface
import "DPI-C" function void my_c_func(input int a, output int b);
import "DPI-C" function int my_c_func_with_ret(input string s);
import "DPI-C" function int sv_fscanf_wrapper(input string path, input string format, output int val);
import "DPI-C" function int sv_sscanf_wrapper(input string str, input string format, output int val);
module DeparamTarget(input logic dt_in, output logic dt_out);
  parameter TARGET_PARAM = 0;
  assign dt_out = dt_in && TARGET_PARAM;
endmodule
module MainModuleForDefparam(input logic mfd_in, output logic mfd_out);
  DeparamTarget inst_defparam_target();
  defparam inst_defparam_target.TARGET_PARAM = 1;
  assign mfd_out = inst_defparam_target.dt_out;
endmodule
module DataTypeModule(
  input logic [3:0] in_data_dt,
  output logic [7:0] out_data_dt
);
  logic [7:0] packed_array[4];
  logic unpacked_array [2];
  logic [15:0] dyn_arr[];
  logic [15:0] assoc_arr[*];
  int queue_dt[$];
  logic fixed_size_array[8];
  struct {
    int s_member_a;
    logic [7:0] s_member_b;
  } my_struct_inst;
  typedef struct packed {
    logic [3:0] field1;
    logic [3:0] field2;
  } my_struct_type;
  my_struct_type another_struct_inst;
  enum {
    STATE_IDLE_DT,
    STATE_ACTIVE_DT,
    STATE_DONE_DT
  } fsm_state_dt;
  parameter type ParamT_dt = int;
  ParamT_dt param_type_var_dt;
  var logic implicit_var_dt;
  integer basic_int_dt;
  logic [31:0] basic_logic_vec_dt;
  real basic_real_dt;
  string basic_string_dt;
  time basic_time_dt;
  byte basic_byte_dt;
  const logic [7:0] CONST_VAL_DT = 8'd255;
  typedef logic [in_data_dt-1:0] custom_width_t_dt;
  custom_width_t_dt custom_var_dt;
  my_class my_class_handle_dt;
  my_interface my_if_inst_dt();
  int func_val_in_dt, func_val_out_dt;
  logic [7:0] pkg_byte_val_dt;
  pkg_byte_t pkg_type_var_dt;
  function void my_void_func_dt();
  endfunction
  always_comb begin
    packed_array = '{8'd0, 8'd1, 8'd2, 8'd3};
    unpacked_array = '{1'b0, 1'b1};
    fixed_size_array = '{0,1,2,3,4,5,6,7};
    out_data_dt = {>>8{in_data_dt}};
    my_struct_inst.s_member_a = 10;
    my_struct_inst.s_member_b = 8'hAA;
    another_struct_inst.field1 = in_data_dt;
    another_struct_inst.field2 = 4'b1111;
    fsm_state_dt = STATE_ACTIVE_DT;
    param_type_var_dt = 20;
    implicit_var_dt = 1'b1;
    basic_int_dt = 123;
    basic_logic_vec_dt = 32'hFEEDFACE;
    basic_real_dt = 3.14159;
    basic_string_dt = "Hello Verilator";
    basic_time_dt = 10ns;
    basic_byte_dt = 8'hBE;
    custom_var_dt = in_data_dt;
    my_class_handle_dt = new(55);
    my_class_handle_dt.class_task(in_data_dt);
    pkg_byte_val_dt = my_package::PKG_PARAM;
    pkg_type_var_dt = 8'hCC;
    my_void_func_dt();
    if (dyn_arr == null) begin
      dyn_arr = new[2];
    end
    if (dyn_arr.size() > 0) dyn_arr[0] = 16'hDEAD;
    queue_dt.push_front(in_data_dt);
    assoc_arr[in_data_dt] = 16'h1234;
    func_val_in_dt = in_data_dt;
    my_if_inst_dt.interface_func_2(func_val_in_dt, func_val_out_dt);
    out_data_dt = out_data_dt + func_val_out_dt;
  end
endmodule
module ExpressionAndStatementModule(
  input logic [7:0] in_expr_stmt,
  input logic [3:0] index_expr_es,
  input logic obj_null_check_es,
  output logic [7:0] out_expr_stmt
);
  logic [15:0] wide_reg_es;
  my_class expr_class_handle_es;
  logic [7:0] const_assign_es;
  logic temp_reg_es;
  string sformat_str_es;
  logic [15:0] temp_arith_result_es;
  (* verilator_trace *) logic trace_me_module_level_es;
  always_comb begin
    const_assign_es = 8'hF0;
    const_assign_es = 10;
    out_expr_stmt = 0;
    out_expr_stmt = in_expr_stmt[index_expr_es+:4];
    wide_reg_es = (16'hFF00 | in_expr_stmt) >> 8;
    out_expr_stmt = in_expr_stmt;
    expr_class_handle_es = null;
    if (obj_null_check_es) begin
      if (expr_class_handle_es == null) begin
        out_expr_stmt = 8'hAA;
      end
    end else begin
      expr_class_handle_es = new(0);
    end
    temp_arith_result_es = wide_reg_es + 1;
    out_expr_stmt = temp_arith_result_es[7:0];
    if (expr_class_handle_es != null) begin
      out_expr_stmt = expr_class_handle_es.class_mem;
    end
    temp_reg_es = 1'b1;
    (* some_verilator_attribute *) out_expr_stmt = in_expr_stmt;
    begin : my_local_scope_es
      int local_var_es = 5;
      out_expr_stmt = out_expr_stmt + local_var_es;
    end
    assert property (@(posedge 1) in_expr_stmt > 0);
    assume property (@(posedge 1) in_expr_stmt < 255);
    trace_me_module_level_es = in_expr_stmt[0];
    sformat_str_es = $sformatf("Input was: %0h", in_expr_stmt);
  end
endmodule
module DPISnippets(
  input int dpi_in,
  output int dpi_out_a,
  output int dpi_out_b,
  output int dpi_out_sscanf_val
);
  int dpi_temp_a, dpi_temp_b;
  string dpi_str_in = "123 456";
  int file_read_val_dpi;
  int sscanf_temp_val;
  always_comb begin
    dpi_out_a = 0;
    dpi_out_b = 0;
    dpi_out_sscanf_val = 0;
    my_c_func(dpi_in, dpi_temp_a);
    dpi_out_a = dpi_temp_a;
    dpi_out_b = my_c_func_with_ret("Hello DPI World");
    sv_fscanf_wrapper("/dev/null", "%d", file_read_val_dpi);
    sv_sscanf_wrapper(dpi_str_in, "%d %d", sscanf_temp_val);
    dpi_out_sscanf_val = sscanf_temp_val;
  end
endmodule
module MySubModule(
  input logic [7:0] sub_in,
  output logic [7:0] sub_out_h
);
  parameter PARAM_VAL_SUB = 5;
  (* verilator_public *) logic [7:0] internal_reg;
  always_comb begin
    internal_reg = sub_in + PARAM_VAL_SUB;
    sub_out_h = internal_reg;
  end
endmodule
module HierarchyModule(
  input logic [7:0] in_h,
  output logic [7:0] out_h
);
  MySubModule sub_inst (.sub_in(in_h), .sub_out_h(out_h));
  function automatic logic [7:0] my_scoped_func_h (input logic [7:0] func_in_h);
    logic [7:0] func_local_var_h = func_in_h + 1;
    return func_local_var_h;
  endfunction
  logic [7:0] func_result_h;
  logic [7:0] var_xref_val;
  always_comb begin
    func_result_h = my_scoped_func_h(in_h);
    var_xref_val = sub_inst.internal_reg;
    out_h = func_result_h + var_xref_val;
  end
endmodule
module VerificationModule(
  input logic [1:0] state_in_vm,
  input bit condition_vm,
  output logic [1:0] result_vm
);
  logic current_state_vm;
  typedef enum { IDLE_VM, START_VM, END_VM } StateEnum_vm;
  StateEnum_vm status_vm;
  (* fsm_state_encoding = "one_hot" *) logic [2:0] one_hot_state_vm;
  input logic clk_vm_proc;
  input logic rst_n_vm_proc;
  reg [1:0] next_state_vm_proc;
  reg [1:0] current_state_ff_vm_proc;
  always_comb begin
    result_vm = 2'b00;
    status_vm = IDLE_VM;
    current_state_vm = state_in_vm[0];
    cover property (state_in_vm == 2'b01);
    assert (state_in_vm != 2'b11);
    one_hot_state_vm = 3'b001;
  end
  always_ff @(posedge clk_vm_proc or negedge rst_n_vm_proc) begin
    if (!rst_n_vm_proc) begin
      current_state_ff_vm_proc <= 2'b00;
    end else begin
      current_state_ff_vm_proc <= next_state_vm_proc;
    end
  end
  always_comb begin
    case (current_state_ff_vm_proc)
      2'b00: next_state_vm_proc = 2'b01;
      2'b01: next_state_vm_proc = 2'b10;
      default: next_state_vm_proc = 2'b00;
    endcase
    result_vm = current_state_ff_vm_proc;
  end
endmodule
module ComplexLogicModule(
    input logic [7:0] in_cl_a,
    input logic [7:0] in_cl_b,
    output logic [7:0] out_cl,
    output logic [7:0] out_stream_cl
);
    logic [7:0] temp_cl;
    logic [15:0] wide_range_var_cl;
    logic [7:0] extracted_val_cl;
    logic [15:0] streamed_val_cl;
    always_comb begin
        temp_cl = in_cl_a + in_cl_b;
        out_cl = temp_cl;
        wide_range_var_cl = {in_cl_a, in_cl_b};
        extracted_val_cl = wide_range_var_cl[15:8];
        streamed_val_cl = {>>1{in_cl_a, in_cl_b}};
        out_stream_cl = streamed_val_cl[7:0];
    end
endmodule
module ForLoopExample(
    input logic [3:0] in_loop,
    output logic [3:0] out_loop_sum
);
    logic [3:0] sum_val = 0;
    genvar i_genvar;
    generate
        for (i_genvar = 0; i_genvar < 4; i_genvar = i_genvar + 1) begin : loop_gen_block
            if (i_genvar == 2) begin : gen_if_block
                localparam DUMMY_PARAM = i_genvar;
            end
        end
    endgenerate
    always_comb begin
        for (int j_loop = 0; j_loop < in_loop; j_loop++) begin
            sum_val = sum_val + j_loop[0];
        end
        out_loop_sum = sum_val;
    end
endmodule
