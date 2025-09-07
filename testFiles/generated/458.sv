module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_c_1755007907317_183,
    input logic [7:0] inj_data_in_1755007907316_814,
    input logic [3:0] inj_data_in_1755007907319_19,
    input logic [31:0] inj_data_in_w_1755007907316_175,
    input logic inj_i_1755007907318_303,
    input logic [1:0] inj_sel_1755007907316_168,
    input wire [1:0] inj_selector_1755007907317_325,
    input wire reset,
    output logic [3:0] inj_data_out_1755007907319_756,
    output logic [31:0] inj_data_out_w_1755007907316_833,
    output logic [31:0] inj_data_out_w_1755007907321_160,
    output logic inj_fs_out_target_1755007907319_100,
    output logic [4:0] inj_internal_out_1755007907317_821,
    output logic [4:0] inj_internal_out_1755007907321_301,
    output logic inj_o_1755007907318_113,
    output logic [7:0] inj_out_1755007907322_875,
    output logic [7:0] inj_out_case_a_1755007907316_434,
    output logic [7:0] inj_out_case_b_1755007907316_366,
    output logic [3:0] inj_out_case_case_1755007907317_819,
    output logic [3:0] inj_out_case_casex_1755007907317_96,
    output logic [3:0] inj_out_case_casez_1755007907317_933,
    output reg inj_out_res_1755007907320_855
);
    // BEGIN: mod_split_case_ts1755007907316
    logic [7:0]  split_case_var_ts1755007907316;
    logic [7:0] other_case_var_ts1755007907316;
        // BEGIN: sub_inst_array_mod_ts1755007907322
        assign inj_out_1755007907322_875 = split_case_var_ts1755007907316;
        // END: sub_inst_array_mod_ts1755007907322

        // BEGIN: case_unique_casez_reordered_mod_ts1755007907321
        always @* begin
            unique casez ({inj_sel_1755007907316_168[0], inj_data_in_1755007907319_19[3:2], inj_sel_1755007907316_168[1]})
                4'b1?0?: inj_internal_out_1755007907321_301 = 30;
                4'b?101: inj_internal_out_1755007907321_301 = 31;  
                4'b0?1?: inj_internal_out_1755007907321_301 = 32;
                4'b1?1?: inj_internal_out_1755007907321_301 = 33;  
                4'b?111: inj_internal_out_1755007907321_301 = 34;  
            endcase
        end
        // END: case_unique_casez_reordered_mod_ts1755007907321

        // BEGIN: ModWideBus_ts1755007907321
        assign inj_data_out_w_1755007907321_160 = ~inj_data_in_w_1755007907316_175;
        // END: ModWideBus_ts1755007907321

        // BEGIN: case_single_default_after_item_ts1755007907320
        always_comb begin
            inj_out_res_1755007907320_855 = 1'b0;
            case (inj_sel_1755007907316_168)
                2'b01: inj_out_res_1755007907320_855 = 1'b1;
                default: inj_out_res_1755007907320_855 = 1'b0;
                2'b10: inj_out_res_1755007907320_855 = 1'b1;
            endcase
        end
        // END: case_single_default_after_item_ts1755007907320

        // BEGIN: child_packed_scalar_port_ts1755007907319
        assign inj_data_out_1755007907319_756 = inj_data_in_1755007907319_19;
        // END: child_packed_scalar_port_ts1755007907319

        mod_fixup_target mod_fixup_target_inst_1755007907319_8195 (
            .fs_in_target(inj_i_1755007907318_303),
            .fs_out_target(inj_fs_out_target_1755007907319_100)
        );
        // BEGIN: top_module_config_dummy_ts1755007907318
        assign inj_o_1755007907318_113 = inj_i_1755007907318_303; 
        // END: top_module_config_dummy_ts1755007907318

        // BEGIN: case_full_simple_mod_ts1755007907318
        always @* begin
            (* full *)
            case (inj_sel_1755007907316_168)
                2'b00: inj_internal_out_1755007907317_821 = 10;
                2'b01: inj_internal_out_1755007907317_821 = 11;
                2'b10: inj_internal_out_1755007907317_821 = 12;
                default: inj_internal_out_1755007907317_821 = 13;
            endcase
        end
        // END: case_full_simple_mod_ts1755007907318

        // BEGIN: CaseStatementConditions_ts1755007907317
        always_comb begin
            case (inj_selector_1755007907317_325)
                2'b00: inj_out_case_case_1755007907317_819 = inj_data_c_1755007907317_183;
                2'b01: inj_out_case_case_1755007907317_819 = inj_data_c_1755007907317_183 + 1;
                2'b10: inj_out_case_case_1755007907317_819 = inj_data_c_1755007907317_183 + 2;
                default: inj_out_case_case_1755007907317_819 = 4'bxxxx;
            endcase
            casez (inj_selector_1755007907317_325)
                2'b0?: inj_out_case_casez_1755007907317_933 = inj_data_c_1755007907317_183 + 10;
                2'b1?: inj_out_case_casez_1755007907317_933 = inj_data_c_1755007907317_183 + 20;
                default: inj_out_case_casez_1755007907317_933 = 4'bzzzz;
            endcase
            casex (inj_selector_1755007907317_325)
                2'b0?: inj_out_case_casex_1755007907317_96 = inj_data_c_1755007907317_183 - 1;
                2'b1?: inj_out_case_casex_1755007907317_96 = inj_data_c_1755007907317_183 - 2;
                default: inj_out_case_casex_1755007907317_96 = 4'bxxxx;
            endcase
        end
        // END: CaseStatementConditions_ts1755007907317

        // BEGIN: ModWideBus_ts1755007907317
        assign inj_data_out_w_1755007907316_833 = ~inj_data_in_w_1755007907316_175;
        // END: ModWideBus_ts1755007907317

    always_comb begin
        split_case_var_ts1755007907316 = 8'hFF;
        other_case_var_ts1755007907316 = 8'hAA;
        case (inj_sel_1755007907316_168)
            2'b00: begin
                split_case_var_ts1755007907316 = inj_data_in_1755007907316_814 + 5;
                other_case_var_ts1755007907316 = inj_data_in_1755007907316_814 + 6;
            end
            2'b01: begin
                split_case_var_ts1755007907316 = inj_data_in_1755007907316_814 - 5;
                other_case_var_ts1755007907316 = inj_data_in_1755007907316_814 - 6;
            end
            default: begin
                split_case_var_ts1755007907316 = inj_data_in_1755007907316_814;
                other_case_var_ts1755007907316 = inj_data_in_1755007907316_814;
            end
        endcase
        inj_out_case_a_1755007907316_434 = split_case_var_ts1755007907316;
        inj_out_case_b_1755007907316_366 = other_case_var_ts1755007907316;
    end
    // END: mod_split_case_ts1755007907316
endmodule

