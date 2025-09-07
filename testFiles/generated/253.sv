interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module always_comb_if (
    input logic cond,
    input logic [31:0] in1,
    input logic [31:0] in2,
    output logic [31:0] out
);
    always_comb begin
        if (cond) begin
            out = in1;
        end else begin
            out = in2;
        end
    end
endmodule

module module_using_package_param (
    input logic [31:0] wide_data_in,
    output logic [31:0] wide_data_out
);
    assign wide_data_out = wide_data_in;
endmodule

module nested_blocks (
    input logic data_value,
    input logic level1_en,
    input logic level2_en,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007838769_894,
    input logic [3:0] inj_case_inside_val_1755007838769_181,
    input logic [15:0] inj_data_in_1755007838769_695,
    input logic inj_data_value_1755007838776_670,
    input logic [31:0] inj_in1_1755007838772_113,
    input logic [7:0] inj_in1_z_1755007838771_18,
    input logic [31:0] inj_in2_1755007838772_840,
    input logic [7:0] inj_in2_z_1755007838771_198,
    input bit [7:0] inj_in_cmd_1755007838770_211,
    input logic inj_in_data_1755007838769_108,
    input logic [2:0] inj_in_val_1755007838768_771,
    input logic inj_level1_en_1755007838776_705,
    input wire reset,
    output logic inj_control_status_1755007838769_60,
    output logic [4:0] inj_internal_out_1755007838769_538,
    output logic [7:0] inj_left_shift_1755007838773_556,
    output logic [7:0] inj_out1_z_1755007838771_74,
    output logic [7:0] inj_out2_z_1755007838771_108,
    output logic [31:0] inj_out_1755007838772_973,
    output logic inj_out_data_pull0_1755007838769_729,
    output logic inj_out_data_pull1_1755007838769_236,
    output reg inj_out_res_1755007838768_39,
    output bit [3:0] inj_out_status_1755007838770_859,
    output logic inj_result_out_1755007838776_153,
    output logic [7:0] inj_right_shift_arith_1755007838773_917,
    output logic [7:0] inj_right_shift_logic_1755007838773_638,
    output logic [31:0] inj_wide_data_out_1755007838775_51
);
    // BEGIN: casez_xz_alt_ts1755007838768
    // BEGIN: module_with_unconnected_drive_ts1755007838769
    // BEGIN: module_conditional_write_ts1755007838769
    // BEGIN: case_priority_casex_complex_mod_ts1755007838770
    // BEGIN: mod_case_standard_ts1755007838770
    // BEGIN: split_diff_vars_branches_ts1755007838771
    // BEGIN: shift_ops_ts1755007838774
    nested_blocks nested_blocks_inst_1755007838776_7073 (
        .level2_en(inj_in_data_1755007838769_108),
        .result_out(inj_result_out_1755007838776_153),
        .data_value(inj_data_value_1755007838776_670),
        .level1_en(inj_level1_en_1755007838776_705)
    );
    module_using_package_param module_using_package_param_inst_1755007838775_870 (
        .wide_data_in(inj_in1_1755007838772_113),
        .wide_data_out(inj_wide_data_out_1755007838775_51)
    );
    assign inj_left_shift_1755007838773_556 = inj_in1_z_1755007838771_18 << inj_in_val_1755007838768_771;
    assign inj_right_shift_logic_1755007838773_638 = inj_in1_z_1755007838771_18 >> inj_in_val_1755007838768_771;
    assign inj_right_shift_arith_1755007838773_917 = inj_in1_z_1755007838771_18 >>> inj_in_val_1755007838768_771;
    // END: shift_ops_ts1755007838774

    always_comb_if always_comb_if_inst_1755007838772_6907 (
        .in2(inj_in2_1755007838772_840),
        .out(inj_out_1755007838772_973),
        .cond(inj_in_data_1755007838769_108),
        .in1(inj_in1_1755007838772_113)
    );
    always @(posedge clk) begin
        if (inj_in_data_1755007838769_108) begin
            inj_out1_z_1755007838771_74 <= inj_in1_z_1755007838771_18;
        end else begin
            inj_out2_z_1755007838771_108 <= inj_in2_z_1755007838771_198;
        end
    end
    // END: split_diff_vars_branches_ts1755007838771

always_comb begin
    case (inj_in_cmd_1755007838770_211)
        8'd0, 8'd1, 8'd2: begin
            inj_out_status_1755007838770_859 = 4'hA;
        end
        8'd3, 8'd4: begin
            inj_out_status_1755007838770_859 = 4'hB;
        end
        default: begin
            inj_out_status_1755007838770_859 = 4'hF;
        end
    endcase
end
    // END: mod_case_standard_ts1755007838770

    always @* begin
        priority casex ({inj_case_expr_1755007838769_894, inj_case_inside_val_1755007838769_181[1:0]})
            4'b1???: inj_internal_out_1755007838769_538 = 24;
            4'b?1??: inj_internal_out_1755007838769_538 = 25;  
            4'b??1?: inj_internal_out_1755007838769_538 = 26;  
            4'b???1: inj_internal_out_1755007838769_538 = 27;  
            4'b0000: inj_internal_out_1755007838769_538 = 28;  
            default: inj_internal_out_1755007838769_538 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007838770

    cond_if cif_inst();
    always_comb begin
        if (inj_in_data_1755007838769_108) begin
            cif_inst.control_reg = inj_data_in_1755007838769_695;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007838769_60 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007838769

    assign inj_out_data_pull1_1755007838769_236 = inj_in_data_1755007838769_108;
    assign inj_out_data_pull0_1755007838769_729 = ~inj_in_data_1755007838769_108;
    // END: module_with_unconnected_drive_ts1755007838769

    always_comb begin
        inj_out_res_1755007838768_39 = 1'b0;
        casez (inj_in_val_1755007838768_771)
            3'b1?z: inj_out_res_1755007838768_39 = 1'b1;
            3'b0z?: inj_out_res_1755007838768_39 = 1'b0;
            default: inj_out_res_1755007838768_39 = 1'b1;
        endcase
    end
    // END: casez_xz_alt_ts1755007838768
endmodule

