module AssignmentCoverage (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] in_force_val,
    input logic [7:0] in_release_val,
    output logic [7:0] out_cont,
    output logic [7:0] out_proc,
    output logic [7:0] out_strength,
    output logic [7:0] out_forced,
    output logic [7:0] out_alias
);
    assign (supply0, supply1) out_strength = in_a + in_b;
    assign out_cont = in_a - in_b;
    always_comb begin
        out_proc = in_a | in_b;
    end
    logic [7:0] force_target_wire;
    always_comb begin
        if (in_a[0]) begin
            force force_target_wire = in_force_val;
        end else begin
            release force_target_wire;
        end
        out_forced = force_target_wire;
    end
    assign out_alias = in_a + in_b;
endmodule
module FuncTaskLifetimeCoverage (
    input logic [15:0] input_val,
    input logic func_enable,
    output logic [15:0] output_val,
    output logic [15:0] task_out,
    output logic [15:0] static_io_output,
    output logic [15:0] static_auto_output
);
    static logic [15:0] module_static_io_dep;
    static logic [15:0] module_static_auto_dep;
    function automatic logic [15:0] get_io_val_from_input(input logic [15:0] val_in_func_arg);
        static logic [15:0] static_io_init;
        static_io_init = val_in_func_arg;
        return static_io_init;
    endfunction
    function automatic logic [15:0] get_auto_val_from_input(input logic [15:0] val_in_func_scope);
        logic [15:0] auto_local_inner = val_in_func_scope + 1;
        static logic [15:0] static_auto_init;
        static_auto_init = auto_local_inner;
        return static_auto_init;
    endfunction
    initial begin
        module_static_io_dep = get_io_val_from_input(input_val);
        module_static_auto_dep = get_auto_val_from_input(input_val);
    end
    function automatic logic [15:0] my_static_func (input logic [15:0] func_in);
        static logic [15:0] static_accumulator = 0;
        static_accumulator = static_accumulator + func_in;
        my_static_func = static_accumulator;
    endfunction
    task my_task (input logic [15:0] task_in, output logic [15:0] task_out_arg);
        task_out_arg = task_in + input_val;
    endtask
    always_comb begin
        if (func_enable) begin
            output_val = my_static_func(input_val);
        end else begin
            output_val = 16'hFFFF;
        end
        static_io_output = module_static_io_dep;
        static_auto_output = module_static_auto_dep;
    end
    always_comb begin
        my_task(input_val + 10, task_out);
    end
endmodule
module RandomizationConstraintCoverage (
    input int unsigned in_seed,
    input logic in_control,
    output int rand_val,
    output int dist_val,
    output int urandom_val,
    output int random_seeded_val
);
    class MyRandomizer;
        rand int my_rand_val;
        rand int my_dist_val;
        int non_rand_member;
        constraint my_c_dist {
            if (in_control) my_dist_val dist {10 := 1, 20 := 2, [30:40] :/ 7};
            else my_dist_val dist {50 := 1, [60:70] := 2};
        }
    endclass
    MyRandomizer my_obj;
    int local_seed_var;
    always_comb begin
        local_seed_var = in_seed;
        if (my_obj == null) begin
            my_obj = new();
            my_obj.my_rand_val = $urandom_range(100, 1);
        end
        my_obj.randomize();
        rand_val = my_obj.my_rand_val;
        dist_val = my_obj.my_dist_val;
        urandom_val = $urandom_range(1000, 100);
        random_seeded_val = $random(local_seed_var);
        my_obj.non_rand_member = in_seed;
    end
endmodule
module FileIOSystemFunctionsCoverage (
    input integer dummy_file_handle_in,
    input int mem_start_addr,
    input string input_string,
    output logic [7:0] mem_target [0:15],
    output int sscanf_out_val,
    output int fscanf_out_val,
    output int ferror_status
);
    integer file_fd_sim_dummy;
    int scanned_from_file;
    logic [7:0] char_for_fungetc = 8'h41;
    string temp_read_line;
    integer fgets_ret;
    string dummy_error_message;
    always_comb begin
        file_fd_sim_dummy = dummy_file_handle_in;
        ferror_status = $ferror(file_fd_sim_dummy, dummy_error_message);
        fgets_ret = $fgets(temp_read_line, file_fd_sim_dummy);
        $fread(mem_target, file_fd_sim_dummy, mem_start_addr, mem_start_addr + 1);
        $fscanf(file_fd_sim_dummy, "%d", scanned_from_file);
        fscanf_out_val = scanned_from_file;
        $fungetc(char_for_fungetc, file_fd_sim_dummy);
        $sscanf(input_string, "%d", sscanf_out_val);
        $readmemh("dummy_mem.mem", mem_target, mem_start_addr, mem_start_addr + 15);
    end
endmodule
module PlusArgsSformatCoverage (
    input string plusarg_search_str,
    input int format_arg,
    output bit test_plusarg_res,
    output int value_plusarg_out,
    output string sformatf_out_str
);
    always_comb begin
        test_plusarg_res = $test$plusargs(plusarg_search_str);
        $value$plusargs("my_int_val=%0d", value_plusarg_out);
        sformatf_out_str = $sformatf("Value: %0d", format_arg);
    end
endmodule
module OperatorSelectCoverage (
    input int in_arr_index,
    input int in_struct_val_a,
    input int in_struct_val_b,
    input logic [7:0] in_pre_val,
    input logic [7:0] in_post_val,
    output logic bit_sel_out,
    output logic [3:0] part_sel_out,
    output int arr_ref_out,
    output int struct_mem_out,
    output logic [7:0] pre_inc_out,
    output logic [7:0] post_dec_out,
    output logic [7:0] pre_sub_out,
    output logic [7:0] post_inc_out
);
    logic [7:0] bit_select_var = 8'hAA;
    logic [7:0] part_select_var = 8'hF0;
    int my_array [0:10];
    struct packed {
        int field_a;
        int field_b;
    } my_struct;
    logic [7:0] pre_val_local;
    logic [7:0] post_val_local;
    logic [7:0] pre_val_local_sub;
    logic [7:0] post_inc_local;
    always_comb begin
        pre_val_local = in_pre_val;
        post_val_local = in_post_val;
        pre_val_local_sub = in_pre_val;
        post_inc_local = in_pre_val;
        pre_inc_out = ++pre_val_local;
        post_dec_out = post_val_local--;
        pre_sub_out = --pre_val_local_sub;
        post_inc_out = post_inc_local++;
        bit_select_var[0] = in_pre_val[0];
        bit_sel_out = bit_select_var[0];
        part_select_var[3:0] = in_pre_val[3:0];
        part_sel_out = part_select_var[3:0];
        if (in_arr_index >= 0 && in_arr_index <= 10) begin
            my_array[in_arr_index] = in_struct_val_a;
            arr_ref_out = my_array[in_arr_index];
        end else begin
            arr_ref_out = 0;
        end
        my_struct.field_a = in_struct_val_a;
        my_struct.field_b = in_struct_val_b;
        struct_mem_out = my_struct.field_a + my_struct.field_b;
        if (in_pre_val < 8) begin
            pre_sel_target_var[in_pre_val +: 4] = in_post_val[3:0];
        end else begin
            pre_sel_target_var = 8'h00;
        end
        pre_sel_target_out = pre_sel_target_var;
    end
endmodule
module SpecialCasesCoverage (
    input int dyn_cast_in,
    input bit event_trigger,
    input logic dummy_sys_ignore_ctrl,
    output int dyn_cast_out,
    output bit event_status,
    output int dist_res
);
    event my_event;
    class BaseClass;
        int val;
        function new(int v); val = v; endfunction
    endclass
    class DerivedClass extends BaseClass;
        int derived_val;
        function new(int v, int dv); super.new(v); derived_val = dv; endfunction
    endclass
    class MyDistributor;
        rand int distribution_var;
        constraint dist_c {
            if (dummy_sys_ignore_ctrl) distribution_var dist {100 := 1, [200:300] :/ 5};
            else distribution_var dist {10 := 1, 20 := 2};
        }
    endclass
    BaseClass base_obj;
    DerivedClass derived_obj;
    MyDistributor my_dist_obj;
    always_comb begin
        int cast_success;
        int dummy_bits_val;
        if (event_trigger) begin
            -> my_event;
            event_status = 1;
        end else begin
            event_status = 0;
        end
        if (base_obj == null) begin
            base_obj = new(dyn_cast_in);
        end
        if (derived_obj == null) begin
            derived_obj = new(0, 0);
        end
        cast_success = $cast(derived_obj, base_obj);
        dyn_cast_out = (cast_success && derived_obj != null) ? derived_obj.val : 0;
        dummy_bits_val = $bits(dyn_cast_in);
        if (my_dist_obj == null) begin
            my_dist_obj = new();
        end
        my_dist_obj.randomize();
        dist_res = my_dist_obj.distribution_var;
    end
endmodule
