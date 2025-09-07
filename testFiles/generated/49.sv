typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [3:0] f1;
    logic f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;

interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module dup_literal_param (
    input logic [4:0] index,
    output logic [7:0] final_result
);
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1, temp2;
    assign temp1 = index + CONST_A;
    assign temp2 = index + 10;
    always_comb begin
        logic [7:0] local_temp;
        local_temp = index * CONST_B;
        final_result = temp1 + temp2 + local_temp;
        if (index > 5) begin
            final_result = final_result + 1;
        end else if (index < CONST_C) begin
            final_result = final_result - 1;
        end
        case (index)
            5'd0: final_result = CONST_A;
            5'd1: final_result = 20;
            5'd2: final_result = 10;
            5'd3: final_result = CONST_B;
            5'd4: final_result = CONST_D;
            5'd5: final_result = 8'hFF;
            default: final_result = CONST_E;
        endcase
    end
endmodule

module explicit_non_ansi_ports_module (
    dummy_in_non_ansi,
    named_conn_in,
    dummy_out_non_ansi,
    named_conn_out
);
    input logic named_conn_in;
    output logic named_conn_out;
    input logic dummy_in_non_ansi;
    output logic dummy_out_non_ansi;
    assign named_conn_out = named_conn_in;
    assign dummy_out_non_ansi = dummy_in_non_ansi;
endmodule

module macro_concat_user (
    input logic [3:0] concat_in,
    output logic [7:0] concat_out
);
    `define MAKE_NAME(a,b) a``b
    logic var_signal;
    always_comb begin
        `MAKE_NAME(var,_signal) = concat_in[0];
    end
    assign concat_out = {4'b0, concat_in[3:1], var_signal};
endmodule

module mod_large_array_target (
    input logic in_la,
    output logic out_la
);
    assign out_la = in_la;
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module used_before_declared_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] undeclared_var_ubddm = 8'd5;
    assign out_val = in_val + undeclared_var_ubddm;
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic [3:0] inj_data_in_n_1755004220140_396,
    input logic [38:0] inj_in_packed_for_conv_1755004220147_571,
    input logic [7:0] inj_in_task_data_1755004220137_866,
    input logic [1:0] inj_in_val_1755004220138_817,
    input int inj_in_val_1755004220139_488,
    input logic [4:0] inj_index_1755004220162_417,
    input logic [31:0] inj_input_pa_1755004220154_449,
    input logic inj_named_conn_in_1755004220143_742,
    input logic [15:0] inj_packed_in_1755004220149_217,
    input logic inj_task_en_1755004220137_430,
    input logic [3:0] inj_v2_1755004220141_88,
    input wire reset,
    output logic [7:0] inj_byte_out_1755004220149_664,
    output logic [7:0] inj_concat_out_1755004220157_877,
    output logic [3:0] inj_data_out1_n_1755004220140_605,
    output logic [3:0] inj_data_out2_n_1755004220140_65,
    output logic inj_data_out_1755004220145_636,
    output logic inj_dummy_out_non_ansi_1755004220143_890,
    output logic inj_eq_1755004220141_750,
    output logic [7:0] inj_field0_byte_o_1755004220152_596,
    output logic [7:0] inj_final_result_1755004220162_764,
    output logic inj_named_conn_out_1755004220143_120,
    output logic inj_out_bit_conv_1755004220147_650,
    output int inj_out_int_conv_1755004220147_792,
    output logic inj_out_la_1755004220142_116,
    output reg inj_out_res_1755004220138_387,
    output reg inj_out_res_1755004220160_679,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755004220147_555,
    output int inj_out_val_1755004220139_668,
    output logic [7:0] inj_out_val_1755004220144_891,
    output logic [5:0] inj_out_vec_conv_1755004220147_949,
    output logic [7:0] inj_output_pa_1755004220154_138,
    output logic [7:0] inj_output_pa_element1_1755004220154_377,
    output logic [15:0] inj_packed_out_1755004220149_871,
    output logic inj_sig_out_1755004220140_561,
    output logic inj_task_output_valid_1755004220137_178
);
    // BEGIN: module_task_write_ts1755004220137
    // BEGIN: case_basic_ts1755004220138
    // BEGIN: super_outside_class_diag_mod_ts1755004220139
    // BEGIN: GenerateIfParam_ts1755004220141
    // BEGIN: ModCompareVec_ts1755004220141
    // BEGIN: assign_pattern_lvalue_ts1755004220148
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked_ts1755004220147;
    int int_var_ts1755004220147;
    logic bit_var_ts1755004220147;
    logic [5:0] vec_var_ts1755004220147;
        dup_literal_param dup_literal_param_inst_1755004220162_2636 (
            .index(inj_index_1755004220162_417),
            .final_result(inj_final_result_1755004220162_764)
        );
        // BEGIN: case_single_default_after_item_ts1755004220160
        always_comb begin
            inj_out_res_1755004220160_679 = 1'b0;
            case (inj_in_val_1755004220138_817)
                2'b01: inj_out_res_1755004220160_679 = 1'b1;
                default: inj_out_res_1755004220160_679 = 1'b0;
                2'b10: inj_out_res_1755004220160_679 = 1'b1;
            endcase
        end
        // END: case_single_default_after_item_ts1755004220160

        macro_concat_user macro_concat_user_inst_1755004220157_5622 (
            .concat_out(inj_concat_out_1755004220157_877),
            .concat_in(inj_v2_1755004220141_88)
        );
        // BEGIN: module_packed_array_ts1755004220154
        logic [7:0] my_packed_array[0:3] ;
        always_comb begin
            if (bit_var_ts1755004220147) begin
                my_packed_array[0] = inj_input_pa_1755004220154_449[7:0];
                my_packed_array[1] = inj_input_pa_1755004220154_449[15:8];
                my_packed_array[2] = inj_input_pa_1755004220154_449[23:16];
                my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
            end else begin
                my_packed_array[0] = 8'h0;
                my_packed_array[1] = 8'h0;
                my_packed_array[2] = 8'h0;
                my_packed_array[3] = 8'h0;
            end
            my_packed_array[0][3:0] = inj_v2_1755004220141_88;
        end
        assign inj_output_pa_1755004220154_138 = my_packed_array[3];
        assign inj_output_pa_element1_1755004220154_377 = my_packed_array[1];
        // END: module_packed_array_ts1755004220154

        // BEGIN: typedef_union_mod_ts1755004220152
        typedef union packed {
            logic [15:0] word_ts1755004220152;
            logic [1:0][7:0] byte_fields_ts1755004220152;
        } my_packed_union_t;
        my_packed_union_t my_union_var;
        always_comb begin
            my_union_var.word_ts1755004220152 = inj_packed_in_1755004220149_217;
        end
        assign inj_field0_byte_o_1755004220152_596 = my_union_var.byte_fields_ts1755004220152[0];
        // END: typedef_union_mod_ts1755004220152

        // BEGIN: PackedStructOps_ts1755004220150
        typedef struct packed {
            logic [7:0] low_ts1755004220150;
            logic [7:0] high_ts1755004220150;
        } pair_t;
        pair_t data_pair;
        assign data_pair.high_ts1755004220150 = inj_packed_in_1755004220149_217[15:8];
        assign data_pair.low_ts1755004220150 = inj_in_task_data_1755004220137_866;
        assign inj_byte_out_1755004220149_664 = data_pair.high_ts1755004220150;
        assign inj_packed_out_1755004220149_871[15:8] = data_pair.high_ts1755004220150;
        assign inj_packed_out_1755004220149_871[7:0] = data_pair.low_ts1755004220150 + inj_in_task_data_1755004220137_866;
        // END: PackedStructOps_ts1755004220150

    always_comb begin
        unpacked_s.f1 = inj_in_task_data_1755004220137_866[3:0];
        unpacked_s.f2 = inj_in_task_data_1755004220137_866[4];
        unpacked_s.f3 = inj_in_task_data_1755004220137_866[7:5];
        reg_unpacked_struct_repacked_ts1755004220147 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var_ts1755004220147 = inj_in_packed_for_conv_1755004220147_571[31:0];
        bit_var_ts1755004220147 = inj_in_packed_for_conv_1755004220147_571[32];
        vec_var_ts1755004220147 = inj_in_packed_for_conv_1755004220147_571[38:33];
        inj_out_unpacked_struct_repacked_1755004220147_555 = reg_unpacked_struct_repacked_ts1755004220147;
        inj_out_int_conv_1755004220147_792 = int_var_ts1755004220147;
        inj_out_bit_conv_1755004220147_650 = bit_var_ts1755004220147;
        inj_out_vec_conv_1755004220147_949 = vec_var_ts1755004220147;
    end
    // END: assign_pattern_lvalue_ts1755004220148

    sequential_register sequential_register_inst_1755004220145_671 (
        .reset_n(reset),
        .data_out(inj_data_out_1755004220145_636),
        .clk(clk),
        .data_in(inj_task_en_1755004220137_430),
        .enable_in(inj_named_conn_in_1755004220143_742)
    );
    used_before_declared_diag_mod used_before_declared_diag_mod_inst_1755004220144_3900 (
        .in_val(inj_in_task_data_1755004220137_866),
        .out_val(inj_out_val_1755004220144_891)
    );
    explicit_non_ansi_ports_module explicit_non_ansi_ports_module_inst_1755004220143_3989 (
        .dummy_in_non_ansi(inj_task_en_1755004220137_430),
        .dummy_out_non_ansi(inj_dummy_out_non_ansi_1755004220143_890),
        .named_conn_in(inj_named_conn_in_1755004220143_742),
        .named_conn_out(inj_named_conn_out_1755004220143_120)
    );
    mod_large_array_target mod_large_array_target_inst_1755004220142_962 (
        .out_la(inj_out_la_1755004220142_116),
        .in_la(inj_task_en_1755004220137_430)
    );
    assign inj_eq_1755004220141_750 = (inj_data_in_n_1755004220140_396 == inj_v2_1755004220141_88);
    // END: ModCompareVec_ts1755004220141

    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755004220140_561 = inj_task_en_1755004220137_430;
        end
        else begin : g_false
            assign inj_sig_out_1755004220140_561 = ~inj_task_en_1755004220137_430;
        end
    endgenerate
    // END: GenerateIfParam_ts1755004220141

    split_multiple_blocking split_multiple_blocking_inst_1755004220140_8203 (
        .data_out1_n(inj_data_out1_n_1755004220140_605),
        .data_out2_n(inj_data_out2_n_1755004220140_65),
        .data_in_n(inj_data_in_n_1755004220140_396)
    );
    assign inj_out_val_1755004220139_668 = inj_in_val_1755004220139_488;
    // END: super_outside_class_diag_mod_ts1755004220139

    always_comb begin
        inj_out_res_1755004220138_387 = 1'b0;
        case (inj_in_val_1755004220138_817)
            2'b00: inj_out_res_1755004220138_387 = 1'b0;
            2'b01: inj_out_res_1755004220138_387 = 1'b1;
            2'b10: inj_out_res_1755004220138_387 = 1'b0;
            2'b11: inj_out_res_1755004220138_387 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755004220138

    my_if task_vif_inst();
    task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
        output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
        if (en) begin
            vif_data = data_val;
            vif_valid = 1'b1;
            vif_ready = 1'b0;
        end else begin
            vif_data = 8'h0;
            vif_valid = 1'b0;
            vif_ready = 1'b1;
        end
    endtask
    always_comb begin
        update_vif_signals(inj_task_en_1755004220137_430, inj_in_task_data_1755004220137_866, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        inj_task_output_valid_1755004220137_178 = task_vif_inst.valid;
    end
    // END: module_task_write_ts1755004220137
endmodule

