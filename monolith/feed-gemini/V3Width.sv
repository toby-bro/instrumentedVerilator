typedef struct packed {
  logic [15:0] m1;
  logic [7:0] m2;
} packed_struct_t;
typedef struct {
  logic [7:0] um1;
  logic [7:0] um2;
} unpacked_struct_t;
typedef union packed {
  logic [7:0] u_mem_p;
  logic [7:0] u_mem_p_same_width;
} packed_union_t;
typedef enum {
  RED,
  GREEN,
  BLUE
} my_enum_t;
typedef enum longint {
  VAL_0 = 0,
  VAL_1 = 1000000,
  VAL_2 = 2000000000000000000
} large_enum_range_t;
typedef int my_int_t;
typedef my_int_t my_ref_typedef_t;
typedef struct {
  int dummy_member;
} my_circular_t;
module ArithmeticLogicOps (
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic [8:0] out_add,
  output logic [7:0] out_sub,
  output logic [15:0] out_mul,
  output logic [7:0] out_div,
  output logic [7:0] out_mod,
  output logic out_and,
  output logic out_or,
  output logic out_xor,
  output logic out_not,
  output logic out_log_and,
  output logic out_log_or,
  output logic dummy_signed_add_out,
  output logic dummy_signed_sub_out,
  output logic dummy_signed_mul_out,
  output logic dummy_signed_div_out,
  output logic dummy_signed_mod_out,
  output logic dummy_signed_negate_out
);
  assign out_add = in_a + in_b;
  assign out_sub = in_a - in_b;
  assign out_mul = in_a * in_b;
  assign out_div = in_a / in_b;
  assign out_mod = in_a % in_b;
  assign out_and = &in_a;
  assign out_or = |in_b;
  assign out_xor = ^in_a;
  assign out_not = ~in_a[0];
  assign out_log_and = (in_a[0] && in_b[0]);
  assign out_log_or = (in_a[1] || in_b[1]);
  logic signed [7:0] s_in_a;
  logic signed [7:0] s_in_b;
  logic signed [8:0] s_out_add;
  logic signed [7:0] s_out_sub;
  logic signed [15:0] s_out_mul;
  logic signed [7:0] s_out_div;
  logic signed [7:0] s_out_mod;
  logic signed [7:0] s_out_negate;
  assign s_in_a = $signed(in_a);
  assign s_in_b = $signed(in_b);
  assign s_out_add = s_in_a + s_in_b;
  assign s_out_sub = s_in_a - s_in_b;
  assign s_out_mul = s_in_a * s_in_b;
  assign s_out_div = s_in_a / s_in_b;
  assign s_out_mod = s_in_a % s_in_b;
  assign s_out_negate = -s_in_a;
  always_comb begin
    dummy_signed_add_out = s_out_add;
    dummy_signed_sub_out = s_out_sub;
    dummy_signed_mul_out = s_out_mul;
    dummy_signed_div_out = s_out_div;
    dummy_signed_mod_out = s_out_mod;
    dummy_signed_negate_out = s_out_negate;
  end
endmodule
module CompareAndCond (
  input logic [7:0] val_a,
  input logic [7:0] val_b,
  input real real_a,
  input real real_b,
  input string str_a,
  input string str_b,
  input logic cond_sel,
  output logic eq_out,
  output logic neq_out,
  output logic gt_out,
  output logic gte_out,
  output logic lt_out,
  output logic lte_out,
  output logic eq_case_out,
  output logic neq_case_out,
  output logic eq_real_out,
  output logic neq_real_out,
  output logic gt_real_out,
  output logic eq_string_out,
  output logic type_comp_out,
  output logic [7:0] mux_out,
  output logic is_unknown_val,
  output logic signed_gt_out_val,
  output logic signed_lt_out_val
);
  assign eq_out = (val_a == val_b);
  assign neq_out = (val_a != val_b);
  assign gt_out = (val_a > val_b);
  assign gte_out = (val_a >= val_b);
  assign lt_out = (val_a < val_b);
  assign lte_out = (val_a <= val_b);
  assign eq_case_out = (val_a === val_b);
  assign neq_case_out = (val_a !== val_b);
  assign eq_real_out = (real_a == real_b);
  assign neq_real_out = (real_a != real_b);
  assign gt_real_out = (real_a > real_b);
  assign eq_string_out = (str_a == str_b);
  assign type_comp_out = (type(logic [7:0]) == type(logic signed [7:0]));
  assign mux_out = cond_sel ? val_a : val_b;
  assign is_unknown_val = $isunknown(val_a);
  logic signed [7:0] s_val_a = $signed(val_a);
  logic signed [7:0] s_val_b = $signed(val_b);
  logic signed_gt_out = s_val_a > s_val_b;
  logic signed_lt_out = s_val_a < s_val_b;
  always_comb begin
    signed_gt_out_val = signed_gt_out;
    signed_lt_out_val = signed_lt_out;
  end
endmodule
module SelectReplicateConcat (
  input logic [31:0] data_in,
  input logic [2:0] index_in,
  input logic [7:0] replicate_count_in,
  input string str_part1_in,
  input string str_part2_in,
  output logic [7:0] bit_sel_out,
  output logic [15:0] part_sel_out,
  output logic [31:0] repl_out,
  output logic [15:0] concat_out,
  output string str_repl_out,
  output string str_concat_out,
  output logic [31:0] shift_left_out,
  output logic [31:0] shift_right_out,
  output logic [31:0] shift_right_arith_out
);
  assign bit_sel_out = data_in[index_in + 5 +: 8];
  assign part_sel_out = data_in[15:0];
  assign repl_out = {4{data_in[7:0]}};
  assign concat_out = {data_in[15:8], data_in[7:0]};
  assign str_repl_out = {2{str_part1_in}};
  assign str_concat_out = {str_part1_in, str_part2_in};
  assign shift_left_out = data_in << index_in;
  assign shift_right_out = data_in >> index_in;
  assign shift_right_arith_out = $signed(data_in) >>> index_in;
endmodule
module TypeCastsAndSysFuncs (
  input logic [31:0] data_u,
  input logic [31:0] data_s,
  input real real_val,
  output logic [31:0] unsigned_out,
  output logic [31:0] signed_out,
  output real real_from_int,
  output real real_from_signed_int,
  output int int_from_real,
  output int int_from_real_round,
  output int clog2_out,
  output int urandom_out,
  output int urandom_range_out,
  output int rand_out,
  output logic cast_out_bit,
  output int cast_size_out,
  output int dynamic_cast_success_out
);
  assign unsigned_out = $unsigned(data_s);
  assign signed_out = $signed(data_u);
  assign real_from_int = real'(data_u);
  assign real_from_signed_int = real'($signed(data_s));
  assign int_from_real = int'(real_val);
  assign int_from_real_round = int'(real_val);
  assign clog2_out = $clog2(data_u);
  assign urandom_out = $urandom();
  assign urandom_range_out = $urandom_range(100, 10);
  assign rand_out = int'($urandom_range(100, -100));
  assign cast_out_bit = logic'(data_u[0]);
  assign cast_size_out = 8'(data_u);
  class MyClass; endclass
  MyClass my_obj_null, my_obj_non_null;
  int dynamic_cast_success;
  always_comb begin
    my_obj_non_null = new();
    dynamic_cast_success = $cast(my_obj_null, my_obj_non_null);
    dynamic_cast_success_out = dynamic_cast_success;
  end
endmodule
module StringOps (
  input string in_str,
  input int index,
  input byte char_val,
  output string out_str_putc,
  output byte out_char_getc,
  output string out_substr,
  output int out_compare,
  output int out_icompare,
  output int out_atoi,
  output real out_atoreal,
  output string out_tolower,
  output string out_toupper,
  output int out_len_n,
  output string out_sformat_itoa,
  output string dummy_sformat_itoa_out,
  output string dummy_sformat_hextoa_out,
  output string dummy_sformat_octtoa_out,
  output string dummy_sformat_bintoa_out,
  output string dummy_sformat_realtoa_out
);
  string local_str_var;
  int local_int_for_sformat = 1234;
  string string_literal_123 = "123";
  string string_literal_pi = "3.14159";
  always_comb begin
    local_str_var = in_str;
    out_str_putc = local_str_var;
    if (index >= 0 && index < in_str.len()) begin
      local_str_var.putc(index, char_val);
      out_char_getc = local_str_var.getc(index);
    end else begin
      out_char_getc = 8'h0;
    end
    out_substr = local_str_var.substr(index, index + 2);
  end
  assign out_compare = in_str.compare("test_string");
  assign out_icompare = in_str.icompare("TEST_STRING");
  assign out_atoi = string_literal_123.atoi();
  assign out_atoreal = string_literal_pi.atoreal();
  assign out_tolower = in_str.tolower();
  assign out_toupper = in_str.toupper();
  assign out_len_n = in_str.len();
  assign out_sformat_itoa = $sformatf("%0d", local_int_for_sformat);
  always_comb begin
    dummy_sformat_itoa_out = $sformatf("%0d", local_int_for_sformat);
    dummy_sformat_hextoa_out = $sformatf("%0h", local_int_for_sformat);
    dummy_sformat_octtoa_out = $sformatf("%0o", local_int_for_sformat);
    dummy_sformat_bintoa_out = $sformatf("%0b", local_int_for_sformat);
    dummy_sformat_realtoa_out = $sformatf("%g", 3.14);
  end
endmodule
module DataStructures (
  input logic [7:0] val_0,
  input logic [7:0] val_1,
  input logic [7:0] val_2,
  input logic [7:0] val_3,
  output logic [31:0] packed_array_out,
  output logic [7:0] unpacked_array_element,
  output logic [7:0] dynamic_array_element,
  output logic [7:0] queue_element,
  output logic [7:0] assoc_array_element,
  output logic [7:0] wildcard_array_element,
  output logic [15:0] struct_mem_packed,
  output logic [7:0] struct_mem_unpacked,
  output logic [7:0] union_member_out,
  output logic [7:0] slice_sel_out [1:0]
);
  logic [31:0] packed_array_var = {val_3, val_2, val_1, val_0};
  assign packed_array_out = packed_array_var;
  logic [7:0] unpacked_array [4];
  logic [7:0] my_array_for_slice [3:0];
  always_comb begin
    unpacked_array[0] = val_0;
    unpacked_array[1] = val_1;
    unpacked_array[2] = val_2;
    unpacked_array[3] = val_3;
    unpacked_array_element = unpacked_array[0];
    unpacked_array_element = unpacked_array[1];
    my_array_for_slice = '{val_0, val_1, val_2, val_3};
    slice_sel_out = my_array_for_slice[0:1];
  end
  logic [7:0] dynamic_array [];
  always_comb begin
    dynamic_array = new[2] (unpacked_array);
    dynamic_array_element = dynamic_array[1];
    dynamic_array.delete();
  end
  logic [7:0] queue_var [$];
  always_comb begin
    queue_var = {val_0, val_1};
    queue_var.push_back(val_2);
    queue_element = queue_var.pop_front();
    queue_var.delete(1);
  end
  logic [7:0] assoc_array [*];
  always_comb begin
    assoc_array = '{0:val_0, 1:val_1};
    assoc_array_element = assoc_array[0];
    if (assoc_array.exists(1)) assoc_array.delete(1);
  end
  logic [7:0] wildcard_array [string];
  always_comb begin
    wildcard_array = '{"key1":val_0, "key2":val_1};
    wildcard_array_element = wildcard_array["key1"];
    if (wildcard_array.exists("key2")) wildcard_array.delete("key2");
  end
  packed_struct_t packed_s_var;
  unpacked_struct_t unpacked_s_var;
  always_comb begin
    packed_s_var = '{m1:{val_0, val_1}, m2:val_0};
    struct_mem_packed = packed_s_var.m1;
    unpacked_s_var = '{um1:val_2, um2:val_3};
    struct_mem_unpacked = unpacked_s_var.um1;
  end
  packed_union_t packed_u_var;
  assign packed_u_var = '{.u_mem_p:val_0};
  assign union_member_out = packed_u_var.u_mem_p;
endmodule
module EnumOps (
  input logic [2:0] enum_in_val,
  output my_enum_t enum_out_val,
  output int enum_num,
  output my_enum_t enum_first,
  output my_enum_t enum_last,
  output string enum_name,
  output my_enum_t enum_next_val,
  output my_enum_t enum_prev_val,
  output logic is_enum_valid,
  output logic large_enum_is_valid_out,
  output large_enum_range_t large_enum_next_val_out
);
  my_enum_t enum_var;
  my_enum_t temp_enum_var;
  large_enum_range_t large_enum_var;
  logic large_enum_is_valid;
  large_enum_range_t large_enum_next_val;
  always_comb begin
    enum_var = my_enum_t'(enum_in_val);
    enum_out_val = enum_var;
    enum_num = my_enum_t::num();
    enum_first = my_enum_t::first();
    enum_last = my_enum_t::last();
    enum_name = enum_var.name();
    enum_next_val = enum_var.next();
    enum_prev_val = enum_var.prev();
    is_enum_valid = $cast(temp_enum_var, enum_in_val);
    large_enum_var = large_enum_range_t'(enum_in_val);
    large_enum_is_valid = $cast(large_enum_var, enum_in_val);
    large_enum_next_val = large_enum_var.next();
    large_enum_is_valid_out = large_enum_is_valid;
    large_enum_next_val_out = large_enum_next_val;
  end
endmodule
module ClassAndRand (
  input int rand_seed,
  input logic [7:0] rand_val_in,
  output int rand_result,
  output string rand_state_out,
  output int static_member_out,
  output int rand_mode_get_out
);
  class MyRandClass;
    rand int rand_member_a;
    rand int rand_member_b;
    constraint c_rand_a { rand_member_a inside {[0:100]}; }
  endclass
  MyRandClass my_obj;
  class StaticClass;
    static int static_member;
  endclass
  always_comb begin
    my_obj = new();
    rand_result = 0;
    rand_state_out = "";
    my_obj.srandom(rand_seed);
    if (my_obj.randomize() with { rand_member_b == rand_val_in; }) begin
      rand_result = my_obj.rand_member_a;
    end
    rand_state_out = my_obj.get_randstate();
    my_obj.set_randstate(rand_state_out);
    StaticClass::static_member = rand_val_in;
    static_member_out = StaticClass::static_member;
    if (my_obj.c_rand_a.constraint_mode()) begin
    end
    void'(my_obj.rand_mode(1));
    rand_mode_get_out = my_obj.rand_mode();
    std::randomize();
  end
endmodule
module InterfaceAndTiming (
  input logic clock,
  input logic data,
  input logic data_from_module_input,
  output logic out_data,
  output logic dummy_wait_out
);
  interface my_if (input logic clk);
    logic sig_internal_cb_input;
    logic sig_internal_cb_output;
    logic sig1_int;
    logic sig2_int;
    clocking cb @(posedge clk);
      input sig_internal_cb_input;
      output sig_internal_cb_output;
    endclocking
    function void my_func(int arg);
      sig2_int = arg;
    endfunction
    task my_task(int arg_t);
      sig1_int = arg_t;
    endtask
  endinterface
  my_if if_inst(.clk(clock));
  my_if if_array_inst [2] (.clk(clock));
  always_comb begin
    if_inst.sig_internal_cb_input = data_from_module_input;
    out_data = if_inst.sig1_int;
    void'(if_inst.my_func(1));
    if_inst.my_task(data);
    if_inst.cb.sig_internal_cb_output <= 1'b1;
    out_data = if_inst.cb.sig_internal_cb_input;
  end
  always @(posedge clock) begin
    void'($past(data));
    void'($fell(data));
    void'($rose(data));
    void'($stable(data));
    void'($sampled(data));
    fork
      begin : fork_block_name
      end
    join_none
  end
  always @(posedge clock) begin
    wait (data == 1) dummy_wait_out = 1;
  end
  always @(posedge clock) begin
    disable fork;
  end
  always @(posedge clock) begin
    wait fork;
  end
  reg [7:0] my_memory [0:15];
  reg [7:0] my_assoc_memory [int];
  always_comb begin
    $readmemb("dummy_file.txt", my_memory, 0, 15);
    $readmemh("dummy_assoc.txt", my_assoc_memory, 0, 15);
  end
endmodule
module PatternsAndUnbounded (
  input logic [7:0] val_a,
  input logic [7:0] val_b,
  input logic [7:0] val_c,
  input logic [7:0] val_d,
  output logic [15:0] assign_pattern_packed_struct_member,
  output logic [7:0] assign_pattern_unpacked_struct_member,
  output logic [7:0] assign_pattern_unpacked_array_element,
  output int queue_size_out,
  output int dyn_array_size_out,
  output logic is_unbounded_result,
  output logic [7:0] queue_unbounded_sel_bit,
  output logic [7:0] queue_unbounded_sel_extract
);
  logic [31:0] dummy_concat_var = {val_a, val_b, val_c, val_d};
  packed_struct_t packed_s_var_pattern;
  assign packed_s_var_pattern = '{m1:{val_a, val_b}, m2:val_a};
  assign assign_pattern_packed_struct_member = packed_s_var_pattern.m1;
  unpacked_struct_t unpacked_s_var_pattern;
  assign unpacked_s_var_pattern = '{um1:val_c, um2:val_d};
  assign assign_pattern_unpacked_struct_member = unpacked_s_var_pattern.um2;
  logic [7:0] unpacked_array_pattern [2];
  assign unpacked_array_pattern = '{val_a, val_b};
  assign assign_pattern_unpacked_array_element = unpacked_array_pattern[0];
  logic [7:0] my_queue_for_empty [$];
  always_comb begin
    my_queue_for_empty = {};
    queue_size_out = my_queue_for_empty.size();
  end
  logic [7:0] my_dyn_array_for_new [];
  always_comb begin
    my_dyn_array_for_new = new[2];
    dyn_array_size_out = my_dyn_array_for_new.size();
  end
  assign is_unbounded_result = $isunbounded(3);
  logic [7:0] q_unbounded_test [$];
  always_comb begin
    q_unbounded_test.push_back(val_a);
    q_unbounded_test.push_back(val_b);
    queue_unbounded_sel_bit = q_unbounded_test[$];
    queue_unbounded_sel_extract = q_unbounded_test[$-1];
  end
endmodule
module AssertCoverRestrict (
  input logic property_in,
  input logic clock_for_sva,
  output logic dummy_out
);
  property p_standalone;
    @(posedge clock_for_sva) (property_in);
  endproperty
  property p_assert_trigger; (1); endproperty
  property p_implication;
    logic A_sig;
    logic B_sig;
    (A_sig |-> B_sig);
  endproperty
  always_comb begin
    dummy_out = property_in;
    assert (property_in)
      dummy_out = 1'b1;
    else
      dummy_out = 1'b0;
    restrict property (p_standalone);
  end
  property p_assert_trigger_clocked;
    @(posedge clock_for_sva) (property_in);
  endproperty
  always @(posedge clock_for_sva) begin
    assert property (p_assert_trigger_clocked) dummy_out = 1'b1;
    else dummy_out = 1'b0;
  end
  always @(posedge clock_for_sva) begin
    cover property (p_assert_trigger_clocked) dummy_out = 1'b1;
  end
endmodule
module LoopsAndControl (
  input logic [7:0] loop_limit,
  input logic [7:0] data_value,
  output logic [7:0] sum_out,
  output logic [7:0] array_sum_out
);
  logic [7:0] loop_i;
  logic [7:0] loop_j;
  logic [7:0] my_array [4];
  always_comb begin
    sum_out = 0;
    array_sum_out = 0;
    for (loop_i = 0; loop_i < loop_limit; loop_i = loop_i + 1) begin
      sum_out = sum_out + loop_i;
    end
    loop_i = 0;
    while (loop_i < loop_limit) begin
      sum_out = sum_out + loop_i;
      loop_i = loop_i + 1;
    end
    loop_i = 0;
    repeat (loop_limit) begin
      sum_out = sum_out + loop_i;
      loop_i = loop_i + 1;
    end
    my_array = '{data_value, data_value+1, data_value+2, data_value+3};
    foreach (my_array[loop_j]) begin
      array_sum_out = array_sum_out + my_array[loop_j];
    end
  end
endmodule
module ConditionalStatements (
  input logic [1:0] sel_in,
  input logic [7:0] data_in_a,
  input logic [7:0] data_in_b,
  input int rand_case_weight_a,
  input int rand_case_weight_b,
  output logic [7:0] out_data_if,
  output logic [7:0] out_data_case,
  output logic [7:0] out_data_randcase,
  output logic [7:0] out_data_case_type
);
  typedef enum { A, B } my_enum_type_local;
  always_comb begin
    out_data_if = 0;
    out_data_case = 0;
    out_data_randcase = 0;
    out_data_case_type = 0;
    if (sel_in == 2'b00) begin
      out_data_if = data_in_a;
    end else if (sel_in == 2'b01) begin
      out_data_if = data_in_b;
    end else begin
      out_data_if = 8'hFF;
    end
    case (sel_in)
      2'b00: out_data_case = data_in_a;
      2'b01: out_data_case = data_in_b;
      default: out_data_case = 8'hAA;
    endcase
    case (type(my_enum_type_local))
      type(int): out_data_case_type = 8'h1;
      type(my_enum_type_local): out_data_case_type = 8'h2;
      default: out_data_case_type = 8'h3;
    endcase
    randcase
      rand_case_weight_a : out_data_randcase = data_in_a;
      rand_case_weight_b : out_data_randcase = data_in_b;
      1: out_data_randcase = 8'hCC;
    endcase
  end
endmodule
module DPIAndTimingControl (
  input int in_arg_dpi,
  input logic [3:0] in_event_val,
  input logic clock,
  output int out_ret_dpi,
  output logic implication_result_out
);
  import "DPI-C" function void my_dpi_open_array_func(input int dpi_array[]);
  import "DPI-C" function int my_dpi_fixed_array_func(input int fixed_array[2]);
  int fixed_arr[2];
  int open_arr[];
  assign fixed_arr = '{10, 20};
  assign open_arr = '{in_arg_dpi, in_arg_dpi + 1};
  always_comb begin
    my_dpi_open_array_func(open_arr);
    out_ret_dpi = my_dpi_fixed_array_func(fixed_arr);
    implication_result_out = 1'b0;
  end
  property p_implication_local_clocked;
    @(posedge clock) (in_event_val[0] |-> in_event_val[1]);
  endproperty
  always @(posedge clock) begin
    assert property (p_implication_local_clocked) implication_result_out = 1'b1;
    else implication_result_out = 1'b0;
  end
  always @(posedge in_event_val[0] or negedge in_event_val[1]) begin
  end
  always_ff @(posedge in_event_val[2]) begin
  end
  always_latch begin
  end
endmodule
module PropertyAndReturn (
  input logic prop_input,
  input int func_return_val,
  output logic property_pass_out,
  output int function_ret_out
);
  property simple_prop;
    @(posedge prop_input) (1);
  endproperty
  function automatic int my_return_func (input int val);
    return val * 2;
  endfunction
  always_comb begin
    property_pass_out = 1'b0;
    function_ret_out = my_return_func(func_return_val);
  end
  always @(posedge prop_input) begin
    assert property (simple_prop) property_pass_out = 1'b1;
    else property_pass_out = 1'b0;
  end
endmodule
module FileOpsAndSystemTasks (
  input string filename_in,
  input string file_mode_in,
  input int offset_in,
  input int operation_in,
  input byte char_to_put,
  input int num_read_bytes,
  output int fopen_ret,
  output int ferror_ret,
  output int feof_ret,
  output int ftell_ret,
  output int fseek_ret,
  output int fungetc_ret,
  output int fread_ret,
  output int fscanf_ret,
  output int sscanf_ret,
  output string stacktrace_out,
  output int system_f_ret,
  output int dummy_fgetc_out
);
  int local_fd;
  string read_string_buffer;
  string ferror_msg_var;
  int scan_val_a, scan_val_b;
  reg [7:0] local_memory_for_file_ops [0:15];
  reg [7:0] local_memory_for_file_ops_assoc [int];
  always_comb begin
    local_fd = $fopen(filename_in, file_mode_in);
    fopen_ret = local_fd;
    ferror_ret = $ferror(local_fd, ferror_msg_var);
    feof_ret = $feof(local_fd);
    ftell_ret = $ftell(local_fd);
    fseek_ret = $fseek(local_fd, offset_in, operation_in);
    dummy_fgetc_out = $fgetc(local_fd);
    void'($fgets(read_string_buffer, local_fd));
    fungetc_ret = 0;
    fread_ret = $fread(local_memory_for_file_ops, local_fd, 0, num_read_bytes);
    fscanf_ret = $fscanf(local_fd, "%d %d", scan_val_a, scan_val_b);
    sscanf_ret = $sscanf("10 20", "%d %d", scan_val_a, scan_val_b);
    $fflush(local_fd);
    $fclose(local_fd);
    stacktrace_out = $stacktrace();
    system_f_ret = $system("echo Hello");
    $timeformat(1, 9, "ns", 0);
    $timeformat(1);
    void'($test$plusargs("PLUSARG_TEST"));
    void'($value$plusargs("VALUE_PLUSARG=%d", scan_val_a));
    $info("This is an info message.");
    $warning("This is a warning message.");
    $error("This is an error message.");
    $fatal(1, "This is a fatal error.");
    void'($time);
    void'($realtime);
  end
endmodule
module InternalWidthNodes (
  input logic [7:0] in_data,
  input logic [7:0] in_exponent,
  output logic [15:0] pow_s_out,
  output logic [15:0] pow_u_out,
  output int count_ones_out,
  output int count_bits_out,
  output int conv_str_len_bits,
  output logic dummy_wire_pull_out
);
  assign pow_s_out = $signed(in_data) ** $signed(in_exponent);
  assign pow_u_out = $unsigned(in_data) ** $signed(in_exponent);
  assign count_ones_out = $countones(in_data);
  assign count_bits_out = $countbits(in_data, 1'b0, 1'b1);
  typedef logic [7:0] unpacked_arr_t [2];
  typedef logic [15:0] packed_arr_t;
  typedef logic [7:0] my_queue_t [$];
  typedef logic [7:0] my_dyn_array_t [];
  unpacked_arr_t u_arr_var;
  packed_arr_t p_arr_var;
  my_queue_t q_var;
  my_dyn_array_t d_arr_var;
  logic dummy_wire_pull;
  always_comb begin
    p_arr_var = packed_arr_t'(u_arr_var);
    u_arr_var = unpacked_arr_t'(p_arr_var);
    q_var = my_queue_t'(u_arr_var);
    q_var = my_queue_t'(d_arr_var);
    assign conv_str_len_bits = $bits("Verilator");
    dummy_wire_pull = 1'b1;
    dummy_wire_pull_out = dummy_wire_pull;
  end
endmodule
module GenParams #(parameter int select_gen_val = 1) (output int gen_output);
  parameter P_WIDTH = 8;
  localparam L_OFFSET = 2;
  parameter COMBO_PARAM = P_WIDTH + L_OFFSET;
  genvar i;
  generate
    if (select_gen_val == 1) begin : gen_if_block
      assign gen_output = COMBO_PARAM;
    end else if (select_gen_val == 2) begin : gen_if_block_2
      case (select_gen_val)
        2: assign gen_output = COMBO_PARAM + 1;
        default: assign gen_output = 0;
      endcase
    end else begin : gen_for_block
      for (i = 0; i < 3; i = i + 1) begin : gen_for_loop
        if (i == select_gen_val) assign gen_output = COMBO_PARAM + i;
      end
    end
  endgenerate
endmodule
module UnpackedArrayMethods (
  input logic [7:0] arr_in_0,
  input logic [7:0] arr_in_1,
  input logic [7:0] arr_in_2,
  input logic [7:0] arr_in_3,
  output logic [7:0] array_and_out,
  output logic [7:0] array_or_out,
  output logic [7:0] array_xor_out,
  output int array_sum_out_2,
  output int array_product_out
);
  logic [7:0] my_unpacked_array [4];
  always_comb begin
    my_unpacked_array[0] = arr_in_0;
    my_unpacked_array[1] = arr_in_1;
    my_unpacked_array[2] = arr_in_2;
    my_unpacked_array[3] = arr_in_3;
    array_and_out = my_unpacked_array.and();
    array_or_out = my_unpacked_array.or();
    array_xor_out = my_unpacked_array.xor();
    array_sum_out_2 = my_unpacked_array.sum();
    array_product_out = my_unpacked_array.product();
  end
endmodule
module CaseZX (
  input logic [3:0] in_val,
  output logic out_casez,
  output logic out_casex
);
  always_comb begin
    out_casez = 1'b0;
    out_casex = 1'b0;
    casez (in_val)
      4'b1???: out_casez = 1'b1;
      default: out_casez = 1'b0;
    endcase
    casex (in_val)
      4'bX10Z: out_casex = 1'b1;
      default: out_casex = 1'b0;
    endcase
  end
endmodule
module TypedefRefDType (
    input logic [7:0] in_data,
    output my_int_t out_typedef,
    output my_ref_typedef_t out_ref_typedef,
    output my_circular_t circular_output
);
    assign out_typedef = in_data;
    assign out_ref_typedef = in_data;
    my_circular_t circular_var;
    always_comb begin
        circular_var.dummy_member = 0;
        circular_output = circular_var;
    end
endmodule
module ClassExtendsPackageRef (
    input logic [7:0] data_in,
    output int out_member
);
    class BaseClass;
        int base_member;
    endclass
    class DerivedClass extends BaseClass;
        int derived_member;
    endclass
    DerivedClass der_obj;
    BaseClass base_obj;
    always_comb begin
        der_obj = new();
        der_obj.base_member = data_in;
        der_obj.derived_member = data_in + 1;
        out_member = der_obj.base_member;
        base_obj = new();
    end
endmodule
module TimeImportModule (
    input logic dummy_in,
    output real current_time_out
);
    parameter real MY_TIME_VAL = 10.0;
    assign current_time_out = $realtime;
endmodule
module SystemDoubleFunctions (
    input real in_real_a,
    input real in_real_b,
    output real out_abs,
    output real out_pow_real,
    output real out_atan2,
    output real out_log
);
    assign out_abs = $sqrt(in_real_a * in_real_a);
    assign out_pow_real = $pow(in_real_a, in_real_b);
    assign out_atan2 = $atan2(in_real_a, in_real_b);
    assign out_log = $log(in_real_a);
endmodule
