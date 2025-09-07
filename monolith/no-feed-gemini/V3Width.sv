module MathOps (
  input logic [7:0] a_in,
  input logic [7:0] b_in,
  input bit       cond_in,
  input logic [3:0] shift_amt_in,
  input real      real_a_in,
  input real      real_b_in,
  output logic [7:0] add_out,
  output logic [7:0] sub_out,
  output logic [15:0] mul_out,
  output logic [7:0] div_out,
  output logic [7:0] mod_out,
  output bit         log_and_out,
  output bit         log_or_out,
  output logic [7:0] bit_and_out,
  output logic [7:0] bit_or_out,
  output logic [7:0] bit_xor_out,
  output logic [7:0] shift_l_out,
  output logic [7:0] shift_r_out,
  output logic [7:0] shift_rs_out,
  output bit         eq_out,
  output bit         neq_out,
  output bit         gt_out,
  output bit         gte_out,
  output bit         eq_case_out,
  output bit         neq_case_out,
  output logic [7:0] neg_out,
  output logic [7:0] not_out,
  output logic [7:0] signed_out,
  output logic [7:0] unsigned_out,
  output logic [3:0] clog2_out,
  output logic [63:0] time_out,
  output logic [63:0] const_unsized_out,
  output logic [7:0] cond_assign_out,
  output logic [7:0] zero_repl_out,
  output logic [7:0] long_const_truncated,
  output logic [7:0] const_xz_extended,
  output logic [7:0] add_real_out,
  output bit         log_eq_real_out,
  output bit         red_and_out,
  output bit         red_or_out,
  output bit         red_xor_out,
  output bit         is_unknown_out
);
  assign add_out = a_in + b_in;
  assign sub_out = a_in - b_in;
  assign mul_out = a_in * b_in;
  assign div_out = a_in / b_in;
  assign mod_out = a_in % b_in;
  assign log_and_out = cond_in && (a_in > b_in);
  assign log_or_out = cond_in || (a_in < b_in);
  assign log_eq_real_out = real_a_in == 0.0; 
  assign bit_and_out = a_in & b_in;
  assign bit_or_out = a_in | b_in;
  assign bit_xor_out = a_in ^ b_in;
  assign red_and_out = &a_in; 
  assign red_or_out = |b_in; 
  assign red_xor_out = ^a_in; 
  assign is_unknown_out = $isunknown(a_in); 
  assign shift_l_out = a_in << shift_amt_in;
  assign shift_r_out = a_in >> shift_amt_in;
  assign shift_rs_out = $signed(a_in) >>> shift_amt_in; 
  assign eq_out = a_in == b_in;
  assign neq_out = a_in != b_in;
  assign gt_out = a_in > b_in;
  assign gte_out = a_in >= b_in;
  assign eq_case_out = a_in === b_in; 
  assign neq_case_out = a_in !== b_in; 
  assign neg_out = -a_in;
  assign not_out = ~a_in;
  assign signed_out = $signed(a_in);
  assign unsigned_out = $unsigned(b_in);
  assign clog2_out = $clog2(a_in);
  assign time_out = $time; 
  assign const_unsized_out = 'hFFFFFFFFFFFFFFFF; 
  assign long_const_truncated = 10'd500; 
  assign const_xz_extended = 'hz; 
  assign cond_assign_out = cond_in ? a_in : b_in; 
  assign zero_repl_out = {0{a_in}}; 
  assign add_real_out = real_a_in + real_b_in; 
endmodule
module SelectOps (
  input logic [31:0] data_in,
  input int index_msb_in,
  input int index_lsb_in,
  input int index_plus_in,
  input int index_minus_in,
  input logic [7:0] array_val_in [0:3],
  output logic [7:0] bit_sel_out,
  output logic [7:0] part_sel_out,
  output logic [7:0] plus_sel_out,
  output logic [7:0] minus_sel_out,
  output logic [7:0] array_indexed_out,
  output logic [7:0] dynamic_array_sel_out,
  output logic [7:0] queue_sel_out,
  output logic [15:0] slice_sel_out,
  output logic [7:0] fixed_range_ascending_out 
);
  assign bit_sel_out = data_in[index_lsb_in +: 8]; 
  assign part_sel_out = data_in[index_msb_in : index_lsb_in]; 
  logic [31:0] internal_data = data_in;
  assign plus_sel_out = internal_data[index_plus_in +: 8]; 
  assign minus_sel_out = internal_data[index_minus_in -: 8]; 
  assign array_indexed_out = array_val_in[1]; 
  logic [7:0] dyn_arr_var [];
  always_comb begin
    dyn_arr_var = new [4]; 
    dyn_arr_var[0] = array_val_in[0];
    dyn_arr_var[1] = array_val_in[1];
    dyn_arr_var[2] = array_val_in[2];
    dyn_arr_var[3] = array_val_in[3];
  end
  assign dynamic_array_sel_out = dyn_arr_var[index_lsb_in]; 
  logic [7:0] queue_var [$];
  always_comb begin
    queue_var.push_back(array_val_in[0]);
    queue_var.push_back(array_val_in[1]);
    queue_var.push_back(array_val_in[2]);
  end
  assign queue_sel_out = queue_var[index_lsb_in]; 
  logic [7:0] fixed_arr [0:3];
  assign fixed_arr = array_val_in;
  assign slice_sel_out = fixed_arr[1:2]; 
  logic [7:0] asc_range_test = 8'hAA;
  assign fixed_range_ascending_out = asc_range_test[0:7]; 
endmodule
module ConcatRepl (
  input logic [7:0] data_a,
  input logic [7:0] data_b,
  input logic [7:0] data_c,
  input logic [7:0] data_d,
  input string      str_a_in,
  input string      str_b_in,
  output logic [31:0] wide_concat_out,
  output logic [23:0] replicate_out,
  output string       str_concat_out,
  output string       str_replicate_out
);
  assign wide_concat_out = {data_a, data_b, data_c, data_d}; 
  assign replicate_out = {3{data_a}}; 
  assign str_concat_out = {str_a_in, str_b_in}; 
  assign str_replicate_out = {3{str_a_in}}; 
endmodule
module TypeCastings (
  input logic [31:0] int_val,
  input real         real_val,
  input string       str_val,
  output int         cast_int_from_real_out,
  output real        cast_real_from_int_out,
  output logic [7:0] cast_sized_out,
  output string      cast_str_from_int_out,
  output int         cast_int_from_str_out,
  output logic [15:0] packed_struct_out,
  output logic [7:0] packed_union_out,
  output logic [1:0] enum_val_out,
  output bit         cast_dyn_success_out,
  output logic [31:0] enum_member_width_out 
);
  assign cast_int_from_real_out = int'(real_val); 
  assign cast_real_from_int_out = real'(int_val); 
  assign cast_sized_out = 8'(int_val); 
  assign cast_str_from_int_out = string'(int_val); 
  assign cast_int_from_str_out = int'(str_val);    
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } my_packed_struct_t;
  my_packed_struct_t my_packed_struct;
  assign my_packed_struct = '{field1: int_val[7:0], field2: int_val[15:8]}; 
  assign packed_struct_out = my_packed_struct;
  typedef union packed {
    logic [7:0] ufield1;
    logic [7:0] ufield2;
  } my_packed_union_t;
  my_packed_union_t my_packed_union;
  assign my_packed_union = '{ufield1: int_val[7:0]}; 
  assign packed_union_out = my_packed_union.ufield1; 
  typedef enum logic [1:0] {
    IDLE = 0,
    BUSY = 1,
    TOO_BIG = 4'd10 
  } state_e;
  state_e current_state;
  assign current_state = state_e'(int_val[1:0]); 
  assign enum_val_out = current_state;
  assign enum_member_width_out = TOO_BIG; 
  class Base; endclass
  class Derived extends Base; endclass
  Base b_obj;
  Derived d_obj;
  always_comb begin
    b_obj = new();
    d_obj = new();
  end
  assign cast_dyn_success_out = ($cast(d_obj, b_obj)); 
  bit type_eq_int_int = (type(int_val) == type(1)); 
  bit type_neq_int_real = (type(int_val) != type(1.0)); 
endmodule
module ArrayOps (
  input int             idx_in,
  input logic [7:0]     val_in,
  input string          key_in,
  input logic [7:0]     init_array_val [0:3],
  output int            dyn_arr_size_out,
  output logic [7:0]    dyn_arr_pop_val_out,
  output logic [7:0]    assoc_arr_read_out,
  output int            assoc_arr_size_out,
  output logic          assoc_arr_exists_out,
  output int            queue_size_out,
  output logic [7:0]    queue_pop_front_val_out,
  output logic [7:0]    queue_pop_back_val_out,
  output int            queue_delete_idx_0_val,
  output int            queue_insert_idx_0_val,
  output logic [7:0]    sum_array_out,
  output int            array_countones_out,
  output logic          wildcard_exists_out,
  output logic [15:0] stream_packed_out, 
  output logic [7:0] unpacked_from_stream_out [0:1], 
  output logic [7:0] dynamic_array_concat_out [], 
  output logic [7:0] queue_literal_out [$] 
);
  logic [7:0] dyn_arr [];
  always_comb begin
    dyn_arr = new [4];
    dyn_arr[0] = init_array_val[0];
    dyn_arr[1] = init_array_val[1];
    dyn_arr[2] = init_array_val[2];
    dyn_arr[3] = init_array_val[3];
    dyn_arr_size_out = dyn_arr.size(); 
  end
  assign dyn_arr_pop_val_out = dyn_arr[idx_in]; 
  logic [7:0] assoc_arr [string];
  logic [7:0] temp_assoc_val;
  always_comb begin
    assoc_arr["one"] = 8'd1;
    assoc_arr["two"] = 8'd2;
    if (assoc_arr.exists(key_in)) begin 
      temp_assoc_val = assoc_arr[key_in]; 
    end else begin
      temp_assoc_val = 8'hFF;
    end
    assoc_arr_exists_out = assoc_arr.exists("one"); 
    assoc_arr_size_out = assoc_arr.num(); 
  end
  assign assoc_arr_read_out = temp_assoc_val;
  logic [7:0] my_queue [$];
  always_comb begin
    my_queue.push_back(init_array_val[0]); 
    my_queue.push_front(init_array_val[1]); 
    my_queue.insert(idx_in, init_array_val[2]); 
    queue_size_out = my_queue.size(); 
  end
  assign queue_pop_front_val_out = my_queue.pop_front(); 
  assign queue_pop_back_val_out = my_queue.pop_back(); 
  assign queue_delete_idx_0_val = (my_queue.delete(0), my_queue.size()); 
  assign queue_insert_idx_0_val = (my_queue.insert(0, val_in), my_queue.size()); 
  logic [7:0] fixed_arr_for_reduction [0:3];
  assign fixed_arr_for_reduction[0] = init_array_val[0];
  assign fixed_arr_for_reduction[1] = init_array_val[1];
  assign fixed_arr_for_reduction[2] = init_array_val[2];
  assign fixed_arr_for_reduction[3] = init_array_val[3];
  assign sum_array_out = fixed_arr_for_reduction.sum(); 
  assign array_countones_out = $countones(init_array_val[0]); 
  logic [7:0] wildcard_arr [*];
  always_comb begin
    wildcard_arr["any"] = 8'd10;
    wildcard_arr["other"] = 8'd20;
    wildcard_exists_out = wildcard_arr.exists("any"); 
  end
  logic [7:0] stream_data_in [0:1];
  assign stream_data_in[0] = val_in;
  assign stream_data_in[1] = val_in + 1;
  assign stream_packed_out = {>>{stream_data_in}}; 
  logic [7:0] unpacked_array_from_stream [0:1];
  assign unpacked_array_from_stream = {>>{val_in, val_in+1}}; 
  assign unpacked_from_stream_out = unpacked_array_from_stream; 
  assign dynamic_array_concat_out = {dyn_arr, dyn_arr}; 
  assign queue_literal_out = {my_queue, my_queue}; 
endmodule
module StringMethods (
  input string in_str_1,
  input string in_str_2,
  input int    idx_char_in,
  input int    len_char_in,
  input int    int_to_str_in,
  input real   real_to_str_in,
  output int    len_str_out,
  output string putc_str_out,
  output logic [7:0] getc_char_out,
  output string substr_out,
  output int    compare_str_out,
  output string tolower_str_out,
  output string toupper_str_out,
  output string itoa_str_out,
  output string hextoa_str_out,
  output string octtoa_str_out,
  output string bintoa_str_out,
  output string realtoa_str_out,
  output int    atoi_int_out
);
  string local_str;
  int    local_int;
  real   local_real;
  assign itoa_str_out   = $sformatf("%0d", int_to_str_in);
  assign hextoa_str_out = $sformatf("%0x", int_to_str_in);
  assign octtoa_str_out = $sformatf("%0o", int_to_str_in);
  assign bintoa_str_out = $sformatf("%0b", int_to_str_in);
  assign realtoa_str_out = $sformatf("%g", real_to_str_in);
  assign len_str_out = in_str_1.len(); 
  string putc_temp = in_str_1;
  always_comb begin
    putc_temp.putc(idx_char_in, 8'h41); 
    putc_str_out = putc_temp;
  end
  assign getc_char_out = in_str_1.getc(idx_char_in); 
  assign substr_out = in_str_1.substr(idx_char_in, len_char_in); 
  assign compare_str_out = in_str_1.compare(in_str_2); 
  assign tolower_str_out = in_str_1.tolower(); 
  assign toupper_str_out = in_str_1.toupper(); 
  assign atoi_int_out = $atoi(in_str_1); 
endmodule
module ClassOps (
  input logic enable_rand_in,
  input int local_seed_in,
  output logic rand_success_out,
  output int rand_mode_out,
  output int srandom_result_out,
  output int my_func_out,
  output string get_randstate_out,
  output string set_randstate_out
);
  class MyClass;
    rand logic [7:0] rand_var1;
    rand logic [7:0] rand_var2;
    constraint c1 { rand_var1 > 10; } 
    function new(); 
      rand_var1 = 0;
      rand_var2 = 0;
    endfunction
    function int my_func(); 
      return rand_var1 + rand_var2;
    endfunction
    task my_task(); 
      rand_var1 = rand_var1 + 1;
    endtask
  endclass
  MyClass my_object;
  always_comb begin
    my_object = new(); 
    if (enable_rand_in) begin
      rand_success_out = my_object.randomize(); 
    end else begin
      rand_success_out = 0;
    end
    rand_mode_out = my_object.rand_mode(); 
    srandom_result_out = my_object.srandom(local_seed_in); 
    my_func_out = my_object.my_func(); 
    my_object.my_task(); 
    get_randstate_out = my_object.get_randstate(); 
    set_randstate_out = my_object.set_randstate("some_state_string"); 
    int some_rand_val = $urandom(); 
    int some_rand_range_val = $urandom_range(10, 5); 
    int some_rand_dist_biop = some_rand_val dist {10 := 1, 20 := 2}; 
    int some_rand_dist_triop = some_rand_val dist {10 := 1, [20:30] := 2}; 
    bit some_inside_check = some_rand_val inside {1, 5, [10:15]}; 
  end
endmodule
module ControlFlow (
  input logic [3:0] count_in,
  input logic [3:0] case_sel_in,
  input logic       if_cond_in,
  input logic       while_cond_in,
  input logic [7:0] foreach_arr_in [0:3],
  input logic [31:0] some_param,
  output logic [7:0] for_loop_out,
  output logic [7:0] repeat_loop_out,
  output logic [7:0] while_loop_out,
  output logic [7:0] case_out,
  output logic [7:0] if_out,
  output logic [7:0] foreach_out,
  output bit         default_disable_out,
  output int         randcase_out,
  output int         pow_out
);
  logic [7:0] for_loop_temp = 0;
  logic [7:0] repeat_loop_temp = 0;
  logic [7:0] while_loop_temp = 0;
  logic [7:0] case_temp = 0;
  logic [7:0] if_temp = 0;
  logic [7:0] foreach_temp = 0;
  logic       default_disable_temp = 0;
  int         randcase_temp = 0;
  int         pow_temp = 0;
  always_comb begin
    for_loop_temp = 0;
    repeat_loop_temp = 0;
    while_loop_temp = 0;
    case_temp = 0;
    if_temp = 0;
    foreach_temp = 0;
    default_disable_temp = 0;
    randcase_temp = 0;
    pow_temp = 0;
    for (int i=0; i < count_in; i++) begin 
      for_loop_temp = for_loop_temp + i;
    end
    for_loop_out = for_loop_temp;
    repeat (count_in) begin 
      repeat_loop_temp = repeat_loop_temp + 1;
    end
    repeat_loop_out = repeat_loop_temp;
    int j = 0;
    while (j < count_in && while_cond_in) begin 
      while_loop_temp = while_loop_temp + 1;
      j++;
    end
    while_loop_out = while_loop_temp;
    case (case_sel_in) 
      0: case_temp = 10;
      1: case_temp = 20;
      default: case_temp = 30;
    endcase
    case_out = case_temp;
    randcase 
      1: randcase_temp = 1;
      2: randcase_temp = 2;
    endcase
    randcase_out = randcase_temp;
    if (if_cond_in) begin 
      if_temp = 100;
    end else begin
      if_temp = 200;
    end
    if_out = if_temp;
    foreach (foreach_arr_in[k]) begin 
      foreach_temp = foreach_temp + foreach_arr_in[k];
    end
    foreach_out = foreach_temp;
    default disable iff (if_cond_in) begin
      default_disable_temp = 1;
    end
    default_disable_out = default_disable_temp;
    pow_temp = 2 ** count_in; 
    if ($signed(2) ** $signed(count_in)) pow_temp = 1; 
    pow_out = pow_temp;
  end
endmodule
module SystemTasksAndFuncs (
  input string filename_in,
  input string plusarg_search_str,
  input logic assert_prop_in,
  input logic [7:0] data_for_bits,
  input logic [7:0] int_array_for_bits [0:3],
  input string      type_name_check_str,
  input logic [31:0] mem_val_in [0:1],
  output int file_desc_out,
  output bit plusarg_test_out,
  output int plusarg_value_out,
  output bit assert_result_out,
  output int bits_scalar_out,
  output int bits_array_out,
  output string typename_out,
  output string stack_trace_str_out,
  output string sys_ignore_out_str,
  output int sys_func_out,
  output bit release_out, 
  output bit assign_in_out 
);
  int dummy_file_desc;
  logic [31:0] dummy_out_val;
  logic [7:0] dummy_mem [0:3];
  string dummy_str_out;
  int dummy_int_out;
  real dummy_real_out;
  logic [7:0] some_var_to_release = 8'h00;
  logic [7:0] some_var_to_assign;
  assign file_desc_out = $fopen(filename_in, "w"); 
  always_comb begin
    int fd = $fopen("temp.txt");
    $fgetc(fd); 
    $fget_s(fd, dummy_str_out); 
    $fread(dummy_mem, fd, 0, 4); 
    $ferror(fd, dummy_str_out); 
    $feof(fd); 
    $fflush(fd); 
    $fseek(fd, 0, 0); 
    $ftell(fd); 
    $fungetc(fd, 8'h41); 
    $fscanf(fd, "%d", dummy_int_out); 
    $sscanf("123", "%d", dummy_int_out); 
    $fclose(fd); 
    $readmemb("mem.mem", dummy_mem); 
    $writememh("mem.mem", dummy_mem); 
  end
  assign plusarg_test_out = $test$plusargs(plusarg_search_str); 
  assign plusarg_value_out = $value$plusargs(plusarg_search_str, dummy_out_val); 
  always_comb begin
    assert_result_out = 0;
  end
  assign bits_scalar_out = $bits(data_for_bits); 
  assign bits_array_out = $bits(int_array_for_bits); 
  assign typename_out = $typename(type_name_check_str); 
  assign stack_trace_str_out = $stacktrace(); 
  always_comb begin
    $timeformat(1, 0, "ns", 80); 
  end
  assign sys_ignore_out_str = $sformatf("%s", $sys_ignore(some_param));
  assign sys_func_out = $system("echo hello"); 
  always_comb begin
    $system("ls"); 
  end
  assign some_var_to_assign = some_param[7:0]; 
  assign assign_in_out = some_var_to_assign[0];
  assign some_var_to_release = 8'b1;
  always_comb begin
    release some_var_to_release; 
    release_out = some_var_to_release[0];
  end
endmodule
module AssignmentPatterns (
  input logic [31:0] data_in,
  input logic [7:0] init_val_a,
  input logic [7:0] init_val_b,
  output struct { logic [7:0] f1; logic [7:0] f2; } struct_out,
  output logic [7:0] array_out [0:3],
  output logic [7:0] assoc_map_out [string]
);
  assign struct_out = '{f1: data_in[7:0], f2: data_in[15:8]}; 
  assign array_out = '{data_in[0], data_in[1], data_in[2], data_in[3]}; 
  assign assoc_map_out = '{"key1": init_val_a, default: init_val_b}; 
endmodule
module TimingAndConcurrency (
  input bit clk_in,
  input bit condition_in,
  input int delay_val_in,
  output bit out_reg
);
  logic [7:0] dummy_var = 0;
  always_comb begin
    out_reg = clk_in; 
    fork 
      dummy_var = dummy_var + 1;
    join_none 
    dummy_var = @(posedge clk_in) dummy_var; 
  end
endmodule
module AdvancedTypes (
  input int some_int,
  input logic [7:0] val_for_iface_arr [0:3],
  output int typedef_val_out,
  output int param_type_out,
  output logic [7:0] iface_arr_val_out
);
  typedef int my_int_t;
  my_int_t typed_var = some_int;
  assign typedef_val_out = typed_var;
  parameter type MY_PARAM_TYPE = int;
  MY_PARAM_TYPE p_var = some_int;
  assign param_type_out = p_var;
  interface my_iface;
    logic [7:0] signal;
    modport mp (input signal); 
    clocking cb @(posedge signal); 
      input signal;
    endclocking
  endinterface
  my_iface if_inst();
  assign if_inst.signal = val_for_iface_arr[0]; 
  assign iface_arr_val_out = if_inst.signal;
  assign iface_arr_val_out = if_inst.cb.signal; 
  function void my_void_func(); 
  endfunction
endmodule
