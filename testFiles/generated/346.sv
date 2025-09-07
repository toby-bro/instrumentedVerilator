interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModClockedResetReg (
    input logic clk,
    input logic d,
    input logic rst_n,
    output logic q
);
    always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
    end
endmodule

module module_with_param (
    input logic in,
    output logic named_out
);
    parameter int DELAY = 10;
    logic bind_dummy_in;
    logic bind_dummy_out;
    assign named_out = in;
endmodule

module snippet (
    input wire clk,
    input logic inj_cond_1755007870315_919,
    input logic [7:0] inj_data_in_1755007870315_700,
    input logic [3:0] inj_p_a_1755007870317_292,
    input logic [3:0] inj_p_b_1755007870318_864,
    input logic [1:0] inj_select_case_1755007870319_971,
    input wire reset,
    output logic inj_case_output_ready_1755007870319_860,
    output logic inj_named_out_1755007870324_224,
    output logic [7:0] inj_o1_r_1755007870316_94,
    output logic [7:0] inj_o2_r_1755007870316_91,
    output logic [7:0] inj_o3_r_1755007870316_361,
    output logic [7:0] inj_out_if_a_1755007870315_2,
    output logic [7:0] inj_out_if_b_1755007870315_955,
    output logic inj_out_its_1755007870322_19,
    output logic inj_q_1755007870318_909,
    output logic inj_single_out_1755007870318_459,
    output logic [15:0] inj_sum_out_i_1755007870316_295
);
    // BEGIN: mod_split_if_ts1755007870315
    logic [7:0]  split_if_var_ts1755007870315;
    logic [7:0] other_if_var_ts1755007870315;
        // BEGIN: split_complex_blocking_ts1755007870317
        logic [7:0] t1_r_ts1755007870317, t2_r_ts1755007870317;
            module_with_param module_with_param_inst_1755007870324_5277 (
                .in(inj_cond_1755007870315_919),
                .named_out(inj_named_out_1755007870324_224)
            );
            // BEGIN: ImplicitTimeScaleModule_ts1755007870322
            assign inj_out_its_1755007870322_19 = inj_cond_1755007870315_919;
            // END: ImplicitTimeScaleModule_ts1755007870322

            // BEGIN: module_case_write_ts1755007870320
            my_if case_vif_inst();
            always_comb begin
                case (inj_select_case_1755007870319_971)
                    2'b00: begin
                        case_vif_inst.data = 8'hAA;
                        case_vif_inst.valid = 1'b1;
                        case_vif_inst.ready = 1'b0;
                    end
                    2'b01: begin
                        case_vif_inst.data = inj_data_in_1755007870315_700;
                        case_vif_inst.valid = 1'b0;
                        case_vif_inst.ready = 1'b1;
                    end
                    2'b10: begin
                        case_vif_inst.data = other_if_var_ts1755007870315;
                        case_vif_inst.valid = 1'b1;
                        case_vif_inst.ready = 1'b1;
                    end
                    default: begin
                        case_vif_inst.data = 8'hFF;
                        case_vif_inst.valid = 1'b0;
                        case_vif_inst.ready = 1'b0;
                    end
                endcase
                inj_case_output_ready_1755007870319_860 = case_vif_inst.ready;
            end
            // END: module_case_write_ts1755007870320

            ModClockedResetReg ModClockedResetReg_inst_1755007870318_1151 (
                .d(inj_cond_1755007870315_919),
                .rst_n(reset),
                .q(inj_q_1755007870318_909),
                .clk(clk)
            );
            // BEGIN: multi_port_decl_module_ts1755007870318
            always_comb begin
                inj_single_out_1755007870318_459 = inj_cond_1755007870315_919;
            end
            // END: multi_port_decl_module_ts1755007870318

        always @(*) begin
            t1_r_ts1755007870317 = split_if_var_ts1755007870315 + other_if_var_ts1755007870315;
            inj_o1_r_1755007870316_94 = t1_r_ts1755007870317 - inj_data_in_1755007870315_700;
            t2_r_ts1755007870317 = other_if_var_ts1755007870315 * inj_data_in_1755007870315_700;
            inj_o2_r_1755007870316_91 = t1_r_ts1755007870317 + t2_r_ts1755007870317;
            inj_o3_r_1755007870316_361 = t2_r_ts1755007870317 / 2;
        end
        // END: split_complex_blocking_ts1755007870317

        // BEGIN: split_for_loop_ts1755007870316
        always @(posedge clk) begin
            inj_sum_out_i_1755007870316_295 <= 0;
            for (int i = 0; i < 4; i = i + 1) begin
                inj_sum_out_i_1755007870316_295 <= inj_sum_out_i_1755007870316_295 + inj_data_in_1755007870315_700 + i;
            end
        end
        // END: split_for_loop_ts1755007870316

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var_ts1755007870315 <= 8'b0;
            other_if_var_ts1755007870315 <= 8'b0;
        end else begin
            if (inj_cond_1755007870315_919) begin
                split_if_var_ts1755007870315 <= inj_data_in_1755007870315_700;
                other_if_var_ts1755007870315 <= inj_data_in_1755007870315_700 + 3;
            end else begin
                split_if_var_ts1755007870315 <= inj_data_in_1755007870315_700 - 1;
                other_if_var_ts1755007870315 <= inj_data_in_1755007870315_700 - 2;
            end
        end
    end
    always_comb begin
        inj_out_if_a_1755007870315_2 = split_if_var_ts1755007870315;
        inj_out_if_b_1755007870315_955 = other_if_var_ts1755007870315;
    end
    // END: mod_split_if_ts1755007870315
endmodule

