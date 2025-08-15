module arith_ops_and_conversions (
    input  logic [31:0] a_in,
    input  logic [15:0] b_in,
    input  logic [7:0] c_in,
    input  int          d_in,
    input  longint      e_in,
    input  real         f_in,
    input  logic [3:0]  shift_val_in,
    input  logic [63:0] bits_in,
    input  real         real_val_in,
    output logic [31:0] add_out,
    output logic [31:0] sub_out,
    output logic [63:0] mul_out,
    output int          div_out,
    output int          mod_out,
    output int          pow_out,
    output int          neg_out,
    output logic        not_out,
    output logic [31:0] s_shift_l_out,
    output logic [31:0] s_shift_r_out,
    output logic [31:0] s_shift_rs_out,
    output real         real_add_out,
    output int          real_to_int_out,
    output logic [63:0] real_to_bits_out,
    output real         bits_to_real_out,
    output int          signed_out,
    output int          unsigned_out,
    output int          clog2_out,
    output logic [3:0]  count_bits_out,
    output logic [3:0]  count_ones_out
);
    assign add_out        = a_in + b_in;
    assign sub_out        = a_in - b_in;
    assign mul_out        = a_in * b_in;
    assign div_out        = d_in / e_in;
    assign mod_out        = d_in % e_in;
    assign pow_out        = d_in ** 2;
    assign neg_out        = -d_in;
    assign not_out        = ~c_in[0];
    assign s_shift_l_out  = a_in <<< shift_val_in;
    assign s_shift_r_out  = a_in >>> shift_val_in;
    assign s_shift_rs_out = a_in >> shift_val_in;
    assign real_add_out     = f_in + real_val_in;
    assign real_to_int_out  = $realtoint(real_val_in);
    assign real_to_bits_out = $real_to_bits(real_val_in);
    assign bits_to_real_out = $bits_to_real(bits_in);
    assign signed_out     = $signed(d_in);
    assign unsigned_out   = $unsigned(d_in);
    assign clog2_out      = $clog2(a_in + 1);
    assign count_bits_out = $countbits(a_in, 1);
    assign count_ones_out = $countones(b_in);
endmodule
module logical_and_reduction_ops (
    input  logic [7:0] data_in,
    input  logic       bool1_in,
    input  logic       bool2_in,
    input  logic [7:0] x_val,
    input  real        r_val,
    output logic       log_not_out,
    output logic       log_and_out,
    output logic       log_or_out,
    output logic       red_and_out,
    output logic       red_or_out,
    output logic       red_xor_out,
    output logic       onehot_out,
    output logic       onehot0_out,
    output logic       is_unknown_out,
    output logic       log_eq_out,
    output logic       log_if_out
);
    assign log_not_out    = !bool1_in;
    assign log_and_out    = bool1_in && bool2_in;
    assign log_or_out     = bool1_in || bool2_in;
    assign log_eq_out     = (bool1_in ==? bool2_in);
    assign log_if_out     = bool1_in ? bool2_in : 1'b0;
    assign red_and_out    = &data_in;
    assign red_or_out     = |data_in;
    assign red_xor_out    = ^data_in;
    assign onehot_out     = $onehot(data_in);
    assign onehot0_out    = $onehot0(data_in);
    assign is_unknown_out = $isunknown(x_val);
endmodule
module comparison_ops (
    input  logic [7:0] val1_in,
    input  logic [7:0] val2_in,
    input  int         sval1_in,
    input  int         sval2_in,
    input  real        rval1_in,
    input  real        rval2_in,
    input  string      str1_in,
    input  string      str2_in,
    output logic       eq_out,
    output logic       neq_out,
    output logic       gt_out,
    output logic       gte_out,
    output logic       lt_out,
    output logic       lte_out,
    output logic       gt_s_out,
    output logic       gte_s_out,
    output logic       lt_s_out,
    output logic       lte_s_out,
    output logic       eq_case_out,
    output logic       neq_case_out,
    output logic       eq_wild_out,
    output logic       neq_wild_out,
    output logic       eq_d_out,
    output logic       neq_d_out,
    output logic       lt_d_out,
    output logic       lte_d_out,
    output logic       gt_d_out,
    output logic       gte_d_out,
    output logic       eq_n_out,
    output logic       neq_n_out,
    output logic       lt_n_out,
    output logic       lte_n_out,
    output logic       gt_n_out,
    output logic       gte_n_out,
    output logic       eq_t_out,
    output logic       neq_t_out,
    output int         type_int_id,
    output int         type_integer_id,
    output int         type_real_id
);
    assign eq_out       = val1_in == val2_in;
    assign neq_out      = val1_in != val2_in;
    assign gt_out       = val1_in > val2_in;
    assign gte_out      = val1_in >= val2_in;
    assign lt_out       = val1_in < val2_in;
    assign lte_out      = val1_in <= val2_in;
    assign gt_s_out     = sval1_in > sval2_in;
    assign gte_s_out    = sval1_in >= sval2_in;
    assign lt_s_out     = sval1_in < sval2_in;
    assign lte_s_out    = sval1_in <= sval2_in;
    assign eq_case_out  = 8'hFF === 8'hXX;
    assign neq_case_out = 8'hFF !== 8'hFF;
    assign eq_wild_out  = 8'hF0 ==? 8'hX0;
    assign neq_wild_out = 8'hF0 !=? 8'hXF;
    assign eq_d_out     = rval1_in == rval2_in;
    assign neq_d_out    = rval1_in != rval2_in;
    assign lt_d_out     = rval1_in < rval2_in;
    assign lte_d_out    = rval1_in <= rval2_in;
    assign gt_d_out     = rval1_in > rval2_in;
    assign gte_d_out    = rval1_in >= rval2_in;
    assign eq_n_out     = str1_in == str2_in;
    assign neq_n_out    = str1_in != str2_in;
    assign lt_n_out     = str1_in < str2_in;
    assign lte_n_out    = str1_in <= str2_in;
    assign gt_n_out     = str1_in > str2_in;
    assign gte_n_out    = str1_in >= str2_in;
    assign type_int_id     = type(int).get_type_id();
    assign type_integer_id = type(integer).get_type_id();
    assign type_real_id    = type(real).get_type_id();
    assign eq_t_out        = (type(int).get_type_id() == type(integer).get_type_id());
    assign neq_t_out       = (type(real).get_type_id() != type(int).get_type_id());
endmodule
module concat_and_replication (
    input  logic [7:0] data1_in,
    input  logic [3:0] data2_in,
    input  logic [1:0] rep_val_in,
    input  string      str_in,
    input  int         num_reps_in,
    input  logic [15:0] stream_in_val,
    output logic [11:0] concat_out,
    output logic [7:0]  replication_out,
    output string       str_concat_out,
    output string       str_replication_out,
    output logic [15:0] stream_pack_out,
    output logic [7:0]  stream_unpack_out
);
    assign concat_out          = {data1_in, data2_in};
    assign replication_out     = {2{rep_val_in}};
    assign str_concat_out      = {str_in, "hello"};
    assign str_replication_out = {num_reps_in{str_in}};
    assign stream_pack_out     = {<<{stream_in_val}};
    assign stream_unpack_out   = {>>8{stream_in_val}};
endmodule
typedef struct packed {
    logic [7:0] field1;
    int field2;
} my_packed_struct_t;
typedef struct {
    logic [7:0] field1;
    int field2;
} my_unpacked_struct_t;
module selects_and_member_access (
    input  logic [31:0] vec_in,
    input  int          idx_in,
    input  int          width_in,
    input  int          arr_idx_in,
    input  string       assoc_key_in,
    input  logic [7:0]  slice_arr_in [4],
    output logic [7:0]  bit_select_out,
    output logic [7:0]  extract_select_out,
    output logic [7:0]  plus_select_out,
    output logic [7:0]  minus_select_out,
    output logic [7:0]  array_select_out,
    output int          assoc_select_out,
    output logic [7:0]  slice_select_out [2],
    output int          struct_member_out,
    output int          dummy_out
);
    my_packed_struct_t   packed_struct_var;
    my_unpacked_struct_t unpacked_struct_var;
    int                  assoc_array_local [string];
    int                  wildcard_array_local [string];
    my_packed_struct_t   temp_packed_struct_var;
    my_unpacked_struct_t temp_unpacked_struct_var;
    assign bit_select_out     = vec_in[idx_in];
    assign extract_select_out = vec_in[idx_in + 7 : idx_in];
    assign plus_select_out    = vec_in[idx_in +: 8];
    assign minus_select_out   = vec_in[idx_in -: 8];
    assign array_select_out   = slice_arr_in[arr_idx_in];
    assign slice_select_out   = slice_arr_in[1:0];
    assign dummy_out = idx_in;
    initial begin
        assoc_array_local["key1"] = 100;
        assoc_array_local["key2"] = 200;
        assoc_select_out = assoc_array_local[assoc_key_in];
        wildcard_array_local["1"] = 10;
        wildcard_array_local["A"] = 20;
        packed_struct_var.field1 = 8'hAB;
        packed_struct_var.field2 = 32'h1234_5678;
        unpacked_struct_var.field1 = 8'hCD;
        unpacked_struct_var.field2 = 32'hABCD_EF01;
        struct_member_out  = unpacked_struct_var.field2;
        temp_packed_struct_var.field1 = 8'h11;
        temp_packed_struct_var.field2 = 32'h2222;
        packed_struct_var = temp_packed_struct_var;
        temp_unpacked_struct_var.field1 = 8'h33;
        temp_unpacked_struct_var.field2 = 32'h4444;
        unpacked_struct_var = temp_unpacked_struct_var;
    end
endmodule
module system_functions (
    input  logic [31:0]  arg_in,
    input  string        str_arg_in,
    input  real          r_arg_in,
    input  int           seed_in,
    input  int           range_min_in,
    input  int           range_max_in,
    input  int           file_desc_in,
    output logic [63:0]  time_out,
    output real          realtime_out,
    output int           timeprecision_out,
    output int           timeunit_out,
    output int           clog2_res,
    output int           rand_out,
    output int           urandom_range_out,
    output logic         unbounded_out,
    output logic         is_unbounded_out,
    output string        sformat_str_out,
    output int           ferror_out,
    output int           feof_out,
    output int           fgetc_out,
    output int           fungetc_out,
    output int           fread_out,
    output int           fscanf_out,
    output int           ftell_out,
    output int           fseek_out,
    output int           system_out,
    output int           test_plusargs_out,
    output int           value_plusargs_out,
    output real          time_import_var_out,
    output int           string_len_out,
    output int           string_compare_out,
    output string        string_tolower_out,
    output string        string_toupper_out,
    output int           string_getc_out,
    output string        string_substr_out,
    output int           string_atoi_out,
    output real          string_atoreal_out
);
    parameter int P_TIME_UNIT_1NS = 1;
    logic [7:0] mem [0:3];
    int fd_open;
    int fd_open_mcd;
    real time_import_var;
    int local_fread_val;
    int local_fscanf_val;
    string trace_val;
    string temp_str_var;
    string temp_str_char_arr = "abc";
    assign time_out          = $time;
    assign realtime_out      = $realtime;
    assign timeprecision_out = $timeprecision;
    assign timeunit_out      = $timeunit;
    assign rand_out          = $rand(seed_in);
    assign urandom_range_out = $urandom_range(range_max_in, range_min_in);
    assign unbounded_out     = (arg_in == $);
    assign is_unbounded_out  = $isunbounded(arg_in);
    assign sformat_str_out = $sformatf("Value: %0d, Real: %g", arg_in, r_arg_in);
    initial begin
        time_import_var = $time_import("1.23ms");
        time_import_var_out = time_import_var;
        $sys_ignore(arg_in, str_arg_in);
        trace_val = $stack_trace();
        $dumpvars(0);
        $dumpfile("dump.vcd");
        $dumpon();
        $dumpoff();
        $dumpall();
        $dumpflush();
        $timeformat(-9, 1, " ns", 20);
        fd_open = $fopen("test.txt", "w");
        fd_open_mcd = $fopen("test_mcd.txt");
        $fdisplay(fd_open, "Test line");
        $fflush(fd_open);
        $fclose(fd_open);
        ferror_out  = $ferror(fd_open, 0);
        feof_out    = $feof(fd_open);
        fgetc_out   = $fgetc(fd_open);
        fungetc_out = $fungetc(fd_open, 8'h41);
        fread_out   = $fread(local_fread_val, fd_open);
        fscanf_out  = $fscanf(fd_open, "%d", local_fscanf_val);
        ftell_out   = $ftell(fd_open);
        fseek_out   = $fseek(fd_open, 0, 0);
        system_out        = $system("echo Hello");
        test_plusargs_out  = $test$plusargs("MY_PLUSARG");
        value_plusargs_out = $value$plusargs("ANOTHER_ARG=%d", arg_in);
        $readmemb("mem.mem", mem);
        $writememh("mem_out.mem", mem);
        string_len_out      = str_arg_in.len();
        string_compare_out  = str_arg_in.compare("test");
        string_tolower_out  = str_arg_in.tolower();
        string_toupper_out  = str_arg_in.toupper();
        string_getc_out     = temp_str_char_arr.getc(0);
        temp_str_char_arr.putc(0, 8'h42);
        string_substr_out   = str_arg_in.substr(0, 2);
        string_atoi_out     = "123".atoi();
        string_atoreal_out  = "3.14".atoreal();
    end
endmodule
typedef logic [3:0] my_logic_arr_t [2];
typedef int my_dyn_arr_t [];
typedef int my_assoc_arr_t [string];
typedef int my_queue_t [$];
typedef int my_wildcard_arr_t [*];
typedef enum {
    RED,
    GREEN = 5,
    BLUE
} Color;
typedef int MY_CONST_INT;
const MY_CONST_INT my_const_var = 123;
module array_and_queue_definitions_and_methods (
    input  logic [7:0] data_in,
    input  int         idx_in,
    input  string      key_in,
    input  int         val_in,
    output int         dyn_size_out,
    output int         queue_size_out,
    output int         assoc_size_out,
    output int         wildcard_size_out,
    output int         arr_sum_out,
    output int         q_pop_front_val,
    output int         q_pop_back_val,
    output string      enum_name_out
);
    Color my_color_var;
    my_dyn_arr_t         dynamic_arr_local;
    my_assoc_arr_t       associative_arr_local;
    my_wildcard_arr_t    wildcard_arr_local;
    my_queue_t           my_queue_local;
    my_logic_arr_t       logic_arr_var_local;
    parameter int COLOR_NUM = Color::num();
    parameter Color COLOR_FIRST = Color::first();
    parameter Color COLOR_LAST = Color::last();
    initial begin
        dynamic_arr_local = new [idx_in];
        dynamic_arr_local[0] = val_in;
        dyn_size_out = dynamic_arr_local.size();
        dynamic_arr_local.delete();
        my_queue_local = {};
        my_queue_local.push_back(val_in);
        my_queue_local.push_front(val_in + 1);
        my_queue_local.insert(0, val_in + 2);
        q_pop_front_val = my_queue_local.pop_front();
        q_pop_back_val  = my_queue_local.pop_back();
        my_queue_local.delete(idx_in);
        queue_size_out = my_queue_local.size();
        associative_arr_local[key_in] = val_in;
        assoc_size_out = associative_arr_local.num();
        if (associative_arr_local.exists(key_in)) begin
            associative_arr_local.delete(key_in);
        end
        associative_arr_local.delete();
        int first_key, last_key, next_key, prev_key;
        if (associative_arr_local.first(first_key)) begin end
        if (associative_arr_local.last(last_key)) begin end
        if (associative_arr_local.next(first_key, next_key)) begin end
        if (associative_arr_local.prev(last_key, prev_key)) begin end
        wildcard_arr_local["1"] = 1;
        wildcard_size_out = wildcard_arr_local.size();
        if (wildcard_arr_local.exists(key_in)) begin end
        wildcard_arr_local.delete();
        logic_arr_var_local[0] = data_in[3:0];
        logic_arr_var_local[1] = data_in[7:4];
        arr_sum_out = logic_arr_var_local.sum();
        my_color_var = Color'($unsigned(val_in));
        enum_name_out = my_color_var.name();
        my_color_var = my_color_var.next(1);
        my_color_var = my_color_var.prev(1);
    end
endmodule
module struct_union_and_patterns (
    input  logic [7:0] byte_in,
    input  int         int_in,
    input  string      str_in,
    input  real        real_in,
    output int         struct_field_out,
    output int         union_field_out,
    output int         packed_struct_res,
    output int         packed_union_res
);
    typedef struct packed {
        logic [7:0] byte_field;
        int         int_field;
    } PackedStruct;
    typedef union packed {
        logic [7:0] byte_field;
        int         int_field;
    } PackedUnion;
    typedef struct {
        logic [7:0] byte_field;
        int         int_field;
    } UnpackedStruct;
    typedef union {
        logic [7:0] byte_field;
        int         int_field;
    } UnpackedUnion;
    PackedStruct   ps_var;
    PackedUnion    pu_var;
    UnpackedStruct us_var;
    UnpackedUnion  uu_var;
    logic [7:0]    arr_byte_in [2];
    int            dyn_arr_pat_val [];
    int            q_pat_val [$];
    int            assoc_pat_val [string];
    int            wildcard_pat_val [string];
    logic [7:0]    basic_vec_pat_val;
    initial begin
        us_var = '{byte_field: byte_in, int_field: int_in};
        us_var = '{byte_in, int_in};
        us_var = '{default: '0};
        us_var = '{int: int_in};
        ps_var = '{byte_field: byte_in, int_field: int_in};
        ps_var = '{default: '0};
        uu_var = '{byte_field: byte_in};
        uu_var = '{int_in};
        pu_var = '{byte_field: byte_in};
        pu_var = '{int_field: int_in};
        arr_byte_in = '{byte_in, byte_in};
        dyn_arr_pat_val = new [3] ('{1, 2, 3});
        q_pat_val = {4, 5, 6};
        assoc_pat_val = '{"key": 10, "another_key": 20, default: '0};
        wildcard_pat_val = '{"any_key": 100, default: '0};
        basic_vec_pat_val = '{1'b1, 1'b0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0};
        struct_field_out = us_var.int_field;
        union_field_out = uu_var.int_field;
        packed_struct_res = ps_var;
        packed_union_res = pu_var;
    end
endmodule
module class_features (
    input int class_seed_in,
    output int class_rand_val,
    output int new_class_val
);
    class MyClass;
        rand int val;
        int another_val;
        constraint c1 { val > 0; };
        function new(int init_val);
            val = init_val;
            another_val = init_val;
        endfunction
        function void set_another_val(int new_val);
            another_val = new_val;
        endfunction
    endclass
    MyClass my_obj;
    MyClass my_copy_obj;
    initial begin
        my_obj = new(10);
        my_obj.randomize();
        my_obj.srandom(class_seed_in);
        int rand_mode_val = my_obj.rand_mode();
        my_obj.rand_mode(0);
        int constraint_mode_val = my_obj.constraint_mode();
        my_obj.constraint_mode(0);
        my_obj.set_another_val(20);
        class_rand_val = my_obj.val;
        new_class_val = my_obj.another_val;
        my_copy_obj = new(my_obj);
    end
endmodule
module control_flow_statements (
    input  logic       cond_in,
    input  logic [7:0] case_sel_in,
    input  int         loop_iter_in,
    input  int         foreach_array [4],
    input  logic       wait_cond_in,
    input  int         event_in,
    input  int         prop_val_in,
    input  logic       disable_cond_in,
    output logic [1:0] if_out,
    output logic [1:0] case_out,
    output int         for_loop_out,
    output int         repeat_loop_out,
    output int         while_loop_out,
    output int         foreach_sum_out,
    output int         fork_join_out,
    output int         return_val_out,
    output logic       assertion_out,
    output logic       coverage_out,
    output logic       implication_out
);
    int local_if_out;
    int local_case_out;
    int local_for_loop_out;
    int local_repeat_loop_out;
    int local_while_loop_out;
    int local_foreach_sum_out;
    int local_fork_join_out;
    int local_return_val;
    logic local_assertion_out;
    logic local_coverage_out;
    function automatic int my_func(int arg);
        return_val_out = arg + 1;
        return arg + 1;
    endfunction
    event my_event;
    property my_property;
        @(posedge event_in) (prop_val_in > 0);
    endproperty
    property implication_prop;
        @(posedge event_in) (prop_val_in > 0) |-> (prop_val_in < 10);
    endproperty
    default disable iff (disable_cond_in);
    initial begin
        if (cond_in) begin
            local_if_out = 1;
        end else begin
            local_if_out = 0;
        end
        case (case_sel_in)
            8'h01 : local_case_out = 1;
            8'h02 : local_case_out = 2;
            default : local_case_out = 0;
        endcase
        case (loop_iter_in)
            0 : begin end
            1 : begin end
            default : begin end
        endcase
        randcase
            10 : begin local_case_out = 10; end
            20 : begin local_case_out = 20; end
            1 : begin local_case_out = 0; end
        endcase
        local_for_loop_out = 0;
        for (int i = 0; i < loop_iter_in; i++) begin
            local_for_loop_out += i;
        end
        local_repeat_loop_out = 0;
        repeat (loop_iter_in) begin
            local_repeat_loop_out++;
        end
        local_while_loop_out = 0;
        while (local_while_loop_out < loop_iter_in) begin
            local_while_loop_out++;
        end
        local_foreach_sum_out = 0;
        foreach (foreach_array[i]) begin
            local_foreach_sum_out += foreach_array[i];
        end
        fork : my_fork_block
            local_fork_join_out = 1;
            local_fork_join_out = local_fork_join_out + 1;
        join_none
        assert property (my_property);
        cover property (my_property);
        assert property (implication_prop);
        local_return_val = my_func(5);
        if_out = local_if_out;
        case_out = local_case_out;
        for_loop_out = local_for_loop_out;
        repeat_loop_out = local_repeat_loop_out;
        while_loop_out = local_while_loop_out;
        foreach_sum_out = local_foreach_sum_out;
        fork_join_out = local_fork_join_out;
        return_val_out = local_return_val;
        assertion_out = 1'b1;
        coverage_out = 1'b1;
        implication_out = 1'b1;
    end
    always_ff @(posedge event_in) begin
        wait (wait_cond_in);
    end
endmodule
module basic_data_types (
    input  int           int_val_in,
    input  bit           bit_val_in,
    input  byte          byte_val_in,
    input  shortint      shortint_val_in,
    input  longint       longint_val_in,
    input  real          real_val_in,
    input  realtime      realtime_val_in,
    input  string        string_val_in,
    input  chandle       chandle_val_in,
    input  event         event_val_in,
    input  logic [3:0]   logic_val_in,
    input  logic [7:0]   logic_ranged_val_in,
    output logic [31:0]  int_out,
    output bit           bit_out,
    output byte          byte_out,
    output shortint      shortint_out,
    output longint       longint_out,
    output real          real_out,
    output realtime      realtime_out,
    output string        string_out,
    output chandle       chandle_out,
    output event         event_out,
    output logic [3:0]   logic_out,
    output logic [7:0]   logic_ranged_out
);
    logic implicit_logic;
    assign int_out          = int_val_in;
    assign bit_out          = bit_val_in;
    assign byte_out         = byte_val_in;
    assign shortint_out     = shortint_val_in;
    assign longint_out      = longint_val_in;
    assign real_out         = real_val_in;
    assign realtime_out     = realtime_val_in;
    assign string_out       = string_val_in;
    assign chandle_out      = chandle_val_in;
    assign event_out        = event_val_in;
    assign logic_out        = logic_val_in;
    assign logic_ranged_out = logic_ranged_val_in;
    assign implicit_logic   = 1'b1;
endmodule
module type_conversion_and_unpacked_array_handling (
    input logic [7:0] unpacked_data_in [2],
    input int         convert_int_in,
    input real        convert_real_in,
    input string      convert_string_in,
    output logic [15:0] packed_array_cvt_out,
    output logic [7:0] unpacked_from_packed_cvt_out [2],
    output int         unpacked_to_queue_cvt_out [$],
    output int         cast_int_out,
    output real        cast_real_out,
    output string      cast_string_out
);
    logic [15:0] packed_version_of_unpacked;
    logic [7:0] unpacked_version_of_packed [2];
    int q_from_unpacked [$];
    logic [7:0] sized_cast_val;
    real temp_real_conv;
    initial begin
        packed_version_of_unpacked = {unpacked_data_in[1], unpacked_data_in[0]};
        packed_array_cvt_out = packed_version_of_unpacked;
        unpacked_version_of_packed = packed_array_cvt_out;
        unpacked_from_packed_cvt_out = unpacked_version_of_packed;
        q_from_unpacked = unpacked_data_in;
        unpacked_to_queue_cvt_out = q_from_unpacked;
        cast_int_out = int'(convert_real_in);
        cast_real_out = real'(convert_int_in);
        cast_string_out = string'(convert_int_in);
        sized_cast_val = 8'(convert_int_in);
        temp_real_conv = convert_int_in;
    end
endmodule
