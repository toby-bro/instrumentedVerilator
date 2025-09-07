interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module basic_comb (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1
);
    ;
    logic [7:0] temp_wire;
    assign temp_wire = in1 + in2;
    always_comb begin
        out1 = temp_wire;
    end
endmodule

module case_parallel_simple_mod (
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        (* parallel *)
        case (case_inside_val)
            4'd0, 4'd1: internal_out = 14;
            4'd2, 4'd3: internal_out = 15;
            default: internal_out = 18;
        endcase
    end
endmodule

module mod_logical_not (
    input logic cond_in,
    output logic cond_out
);
    always_comb begin
        cond_out = !cond_in;
    end
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input logic [3:0] inj_case_inside_val_1755007791934_576,
    input logic [7:0] inj_in_override_e_1755007791933_235,
    input logic [2:0] inj_in_val_1755007791936_985,
    input logic [7:0] inj_in_vec_1755007791932_855,
    input int inj_index_in_1755007791932_757,
    input logic [31:0] inj_p_in1_1755007791939_185,
    input logic [31:0] inj_p_in2_1755007791939_321,
    input logic [1:0] inj_p_mode_1755007791939_22,
    input logic inj_udnt_input_1755007791932_389,
    input logic inj_uin_1755007791932_923,
    input wire reset,
    output logic inj_cond_out_1755007791947_493,
    output logic [7:0] inj_data_out_1755007791944_907,
    output logic [4:0] inj_internal_out_1755007791934_946,
    output logic [7:0] inj_out1_1755007791952_0,
    output logic [7:0] inj_out1_z_1755007791937_728,
    output logic [7:0] inj_out2_z_1755007791937_599,
    output logic [7:0] inj_out_1755007791942_213,
    output logic inj_out_bit_1755007791932_934,
    output logic inj_out_data_q_1755007791935_266,
    output reg inj_out_res_1755007791936_659,
    output logic [3:0] inj_out_slice_1755007791932_94,
    output logic [7:0] inj_out_sum_1755007791949_702,
    output logic [7:0] inj_out_val_e_1755007791933_552,
    output logic [31:0] inj_p_out_1755007791939_806,
    output logic inj_sig_out_1755007791933_811,
    output logic inj_status_e_1755007791933_974,
    output logic inj_tx_status_1755007791940_147,
    output logic inj_udnt_output_1755007791932_864,
    output logic inj_uout_1755007791932_613
);
    // BEGIN: udnt_port_module_ts1755007791932
    // BEGIN: element_select_packed_ts1755007791932
    // BEGIN: GenerateIfParam_ts1755007791933
    // BEGIN: split_mixed_cond_seq_ts1755007791934
    logic [7:0] temp_val_e_ts1755007791934;
        // BEGIN: ModSampledVarLogic_ts1755007791945
        logic [7:0] __Vsampled_state = 8'hAB; 
        logic [7:0] internal_reg_ts1755007791945;
            // BEGIN: simple_for_loop_ts1755007791949
            logic [7:0] sum_ts1755007791949;
                basic_comb basic_comb_inst_1755007791952_9074 (
                    .in2(temp_val_e_ts1755007791934),
                    .out1(inj_out1_1755007791952_0),
                    .in1(inj_in_vec_1755007791932_855)
                );
            always_comb begin
                sum_ts1755007791949 = 8'h00;
                for (int i = 0; i < 5; i = i + 1) begin
                    sum_ts1755007791949 = sum_ts1755007791949 + inj_in_vec_1755007791932_855;
                end
                inj_out_sum_1755007791949_702 = sum_ts1755007791949;
            end
            // END: simple_for_loop_ts1755007791949

            mod_logical_not mod_logical_not_inst_1755007791947_5806 (
                .cond_out(inj_cond_out_1755007791947_493),
                .cond_in(inj_uin_1755007791932_923)
            );
        always @(posedge clk) begin
        if (inj_case_inside_val_1755007791934_576 == 4'd5) begin 
            internal_reg_ts1755007791945 <= __Vsampled_state + inj_case_inside_val_1755007791934_576; 
        end else if (inj_case_inside_val_1755007791934_576 > 4'd8) begin 
            internal_reg_ts1755007791945 <= {4'h0, inj_case_inside_val_1755007791934_576} - 1; 
        end else begin
            internal_reg_ts1755007791945 <= 8'hFF;
        end
        end
        assign inj_data_out_1755007791944_907 = internal_reg_ts1755007791945;
        // END: ModSampledVarLogic_ts1755007791945

        // BEGIN: sequential_always_assign_ts1755007791942
        always @(posedge clk) begin
            inj_out_1755007791942_213 <= inj_in_vec_1755007791932_855;
        end
        // END: sequential_always_assign_ts1755007791942

        // BEGIN: module_struct_write_ts1755007791941
        struct_if stif_inst();
        always_comb begin
            stif_inst.packet_field1 = temp_val_e_ts1755007791934;
            stif_inst.packet_field2 = inj_in_override_e_1755007791933_235;
            stif_inst.tx_en = 1'b1;
            inj_tx_status_1755007791940_147 = stif_inst.tx_en;
        end
        // END: module_struct_write_ts1755007791941

        // BEGIN: more_procedural_ts1755007791939
        always_comb begin
            case (inj_p_mode_1755007791939_22)
                2'b00: inj_p_out_1755007791939_806 = (inj_p_in1_1755007791939_185 + inj_p_in2_1755007791939_321) * 2;
                2'b01: inj_p_out_1755007791939_806 = (inj_p_in1_1755007791939_185 - inj_p_in2_1755007791939_321) / 3; 
                2'b10: inj_p_out_1755007791939_806 = (inj_p_in1_1755007791939_185 << 4) | (inj_p_in2_1755007791939_321 >> 2);
                default: inj_p_out_1755007791939_806 = ~(inj_p_in1_1755007791939_185 ^ inj_p_in2_1755007791939_321) + 1;
            endcase
        end
        // END: more_procedural_ts1755007791939

        // BEGIN: split_diff_vars_branches_ts1755007791937
        always @(posedge clk) begin
            if (inj_udnt_input_1755007791932_389) begin
                inj_out1_z_1755007791937_728 <= inj_in_vec_1755007791932_855;
            end else begin
                inj_out2_z_1755007791937_599 <= temp_val_e_ts1755007791934;
            end
        end
        // END: split_diff_vars_branches_ts1755007791937

        // BEGIN: casez_xz_alt_ts1755007791936
        always_comb begin
            inj_out_res_1755007791936_659 = 1'b0;
            casez (inj_in_val_1755007791936_985)
                3'b1?z: inj_out_res_1755007791936_659 = 1'b1;
                3'b0z?: inj_out_res_1755007791936_659 = 1'b0;
                default: inj_out_res_1755007791936_659 = 1'b1;
            endcase
        end
        // END: casez_xz_alt_ts1755007791936

        module_assign_nonblocking module_assign_nonblocking_inst_1755007791935_1389 (
            .clk(clk),
            .in_value(temp_val_e_ts1755007791934),
            .reset(reset),
            .out_data_q(inj_out_data_q_1755007791935_266)
        );
        case_parallel_simple_mod case_parallel_simple_mod_inst_1755007791934_5276 (
            .case_inside_val(inj_case_inside_val_1755007791934_576),
            .internal_out(inj_internal_out_1755007791934_946)
        );
    always @(posedge clk) begin
        temp_val_e_ts1755007791934 <= inj_in_vec_1755007791932_855 + 5;
        if (inj_udnt_input_1755007791932_389) begin
            inj_out_val_e_1755007791933_552 <= temp_val_e_ts1755007791934;
            inj_status_e_1755007791933_974 <= 1;
        end else begin
            inj_out_val_e_1755007791933_552 <= inj_in_override_e_1755007791933_235;
            inj_status_e_1755007791933_974 <= 0;
        end
    end
    // END: split_mixed_cond_seq_ts1755007791934

    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755007791933_811 = inj_udnt_input_1755007791932_389;
        end
        else begin : g_false
            assign inj_sig_out_1755007791933_811 = ~inj_udnt_input_1755007791932_389;
        end
    endgenerate
    // END: GenerateIfParam_ts1755007791933

    always_comb begin
        if (inj_index_in_1755007791932_757 >= 0 && inj_index_in_1755007791932_757 < 8)
            inj_out_bit_1755007791932_934 = inj_in_vec_1755007791932_855[inj_index_in_1755007791932_757];
        else
            inj_out_bit_1755007791932_934 = 'x; 
    end
    assign inj_out_slice_1755007791932_94 = inj_in_vec_1755007791932_855[6:3];
    // END: element_select_packed_ts1755007791932

    assign inj_uout_1755007791932_613 = inj_uin_1755007791932_923;
    assign inj_udnt_output_1755007791932_864 = inj_udnt_input_1755007791932_389;
    // END: udnt_port_module_ts1755007791932
endmodule

