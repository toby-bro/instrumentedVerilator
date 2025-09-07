module module_pins_and_members (
    input logic [7:0] in_data,
    output logic [7:0] out_data_direct,
    output struct packed { logic [3:0] val1; logic [3:0] val2; } out_struct_port
);
    typedef struct packed {
        logic [7:0] reg_field;
        logic [7:0] wire_field;
    } my_struct_t;
    my_struct_t s_var;
    class MyClass;
        logic [7:0] m_data;
        function new();
            m_data = 8'hAA;
        endfunction
    endclass
    MyClass my_obj;
    always_comb begin
        out_data_direct = in_data;
        s_var.reg_field = in_data[3:0];
        s_var.wire_field = in_data[7:4];
    end
    always_ff @(posedge in_data[0]) begin
        if (my_obj == null) begin
            my_obj = new();
        end
        my_obj.m_data = in_data;
        out_struct_port.val1 = my_obj.m_data[3:0];
        out_struct_port.val2 = my_obj.m_data[7:4];
    end
endmodule
module module_arithmetic_and_selects (
    input logic [7:0] a_in,
    input logic [7:0] b_in,
    input logic [2:0] sel_idx,
    input bit clk_in,
    output logic [7:0] result_inc,
    output logic [7:0] result_dec,
    output logic [7:0] selected_bits,
    output logic selected_bit
);
    logic [7:0] val_pre_inc;
    logic [7:0] val_post_inc;
    logic [7:0] val_pre_dec;
    logic [7:0] val_post_dec;
    initial begin
        val_pre_inc = a_in;
        val_post_inc = b_in;
        val_pre_dec = a_in;
        val_post_dec = b_in;
    end
    always_ff @(posedge clk_in) begin
        val_pre_inc = ++val_pre_inc;
        val_post_inc = val_post_inc++;
        val_pre_dec = --val_pre_dec;
        val_post_dec = val_post_dec--;
        result_inc = val_pre_inc + val_post_inc;
        result_dec = val_pre_dec - val_post_dec;
    end
    always_comb begin
        selected_bits = a_in[6:3];
        selected_bit = b_in[sel_idx];
    end
endmodule
module module_force_release_event (
    input logic [7:0] force_val,
    input logic release_en,
    input logic event_trigger,
    output logic [7:0] forced_var,
    output logic event_status
);
    logic [7:0] internal_var = 8'hAA;
    event my_event;
    assign forced_var = internal_var;
    always_ff @(posedge event_trigger) begin
        if (force_val > 0) begin
            force internal_var = force_val;
        end
        if (release_en) begin
            release internal_var;
        end
        -> my_event;
        event_status = 1'b1;
    end
endmodule
module module_system_functions (
    input bit clk,
    input logic [7:0] input_seed,
    input logic [7:0] data_for_sformatf,
    output logic [31:0] random_out,
    output logic [7:0] sformatf_out_val,
    output logic check_plusargs_out,
    output int read_mem_word,
    output int scanned_data_out,
    output bit cast_success
);
    rand int my_rand_var;
    int rand_val_no_seed;
    int rand_val_with_seed;
    constraint c_my_rand_var {
        my_rand_var inside {[0:100]};
    }
    string sformat_str;
    string scan_str = "Value: 12345";
    int scanned_val;
    logic [7:0] memory [0:15];
    class BaseClass;
    endclass
    class DerivedClass extends BaseClass;
    endclass
    BaseClass base_obj;
    DerivedClass derived_obj;
    task automatic set_static_var_and_test(input int task_input_val);
        static int static_counter = 0;
        int automatic_local_var = task_input_val + 1;
        static_counter = automatic_local_var;
    endtask
    always_ff @(posedge clk) begin
        rand_val_no_seed = $urandom;
        rand_val_with_seed = $urandom(input_seed);
        void'(this.randomize());
        random_out = my_rand_var;
        $sformatf(sformat_str, "Data: %0d", data_for_sformatf);
        sformatf_out_val = data_for_sformatf;
        void'($sscanf(scan_str, "Value: %0d", scanned_val));
        scanned_data_out = scanned_val;
        memory[0] = 8'hAA;
        memory[1] = 8'hBB;
        $readmemh("mem_init.hex", memory, 0, 15);
        read_mem_word = memory[0];
        if ($test$plusargs("MY_TEST_ARG")) begin
            check_plusargs_out = 1'b1;
        end else begin
            check_plusargs_out = 1'b0;
        end
        string plusarg_value;
        void'($value$plusargs("ANOTHER_TEST_ARG=%s", plusarg_value));
        set_static_var_and_test(input_seed);
        if (base_obj == null) begin
            base_obj = new();
            derived_obj = new();
        end
        cast_success = $cast(derived_obj, base_obj);
    end
endmodule
module module_dist_operators (
    input bit clk,
    input logic trigger_randomize,
    output logic [7:0] random_weighted_val_biop,
    output logic [7:0] random_weighted_val_triop
);
    rand logic [7:0] my_rand_dist_biop;
    rand logic [7:0] my_rand_dist_triop;
    constraint dist_biop_c {
        my_rand_dist_biop dist { 1'b0 := 1, [1:7] := 2, 8'hFF := 1 };
    }
    constraint dist_triop_c {
        my_rand_dist_triop dist { 1'b0 := 1, [1:7] := 2, [8:15] := 3, [16:23] := 4, [24:31] := 5, [32:63] := 6, [64:127] := 7, [128:255] := 8 };
    }
    always_ff @(posedge clk) begin
        if (trigger_randomize) begin
            void'(this.randomize());
        end
        random_weighted_val_biop = my_rand_dist_biop;
        random_weighted_val_triop = my_rand_dist_triop;
    end
endmodule
module module_array_references (
    input logic [7:0] in_val,
    input int index_fixed,
    input int index_dyn,
    output logic [7:0] fixed_array_out,
    output logic [7:0] dyn_array_out
);
    logic [7:0] fixed_array [0:15];
    logic [7:0] dyn_array [];
    initial begin
        for (int i=0; i<16; i++) begin
            fixed_array[i] = i;
        end
    end
    always_ff @(posedge in_val[0]) begin
        fixed_array[index_fixed] = in_val;
        fixed_array_out = fixed_array[index_fixed];
        if (index_dyn < 8 && dyn_array.size() == 0) begin
            dyn_array = new[8];
            for (int i=0; i<8; i++) begin
                dyn_array[i] = i * 2;
            end
        end
        if (index_dyn < dyn_array.size()) begin
            dyn_array[index_dyn] = in_val + 1;
            dyn_array_out = dyn_array[index_dyn];
        end else begin
            dyn_array_out = 8'h00;
        end
    end
endmodule
module module_continuous_strength (
    input logic in_signal,
    output logic out_with_strength
);
    assign (strong1, pull0) out_with_strength = in_signal;
endmodule
module module_sys_ignore (
    input logic trigger_in,
    output real current_sim_time
);
    always_comb begin
        if (trigger_in) begin
            current_sim_time = $realtime;
        end else begin
            current_sim_time = 0.0;
        end
    end
endmodule
