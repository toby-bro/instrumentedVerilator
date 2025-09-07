module Comb_IfElse (
    input wire condition,
    input wire [15:0] value1,
    input wire [15:0] value2,
    output reg [15:0] result_val
);
    always_comb begin
        if (condition) begin
            result_val = value1;
        end else begin
            result_val = value2;
        end
    end
endmodule

module generic_class_scope_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    assign out_val = in_val;
endmodule

module mod_case_standard (
    input bit [7:0] in_cmd,
    output bit [3:0] out_status
);
always_comb begin
    case (in_cmd)
        8'd0, 8'd1, 8'd2: begin
            out_status = 4'hA;
        end
        8'd3, 8'd4: begin
            out_status = 4'hB;
        end
        default: begin
            out_status = 4'hF;
        end
    endcase
end
endmodule

module nested_module (
    input logic nm_in,
    output logic nm_out
);
    assign nm_out = nm_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_b_1755007830400_455,
    input logic [1:0] inj_case_expr_1755007830400_206,
    input logic inj_data0_1755007830400_349,
    input int inj_dummy_in_1755007830400_396,
    input logic inj_i_in_1755007830399_789,
    input bit [7:0] inj_in_cmd_1755007830401_167,
    input logic [7:0] inj_in_val_1755007830400_140,
    input wire [15:0] inj_value1_1755007830400_88,
    input wire [15:0] inj_value2_1755007830400_369,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007830400_737,
    output logic inj_nm_out_1755007830401_632,
    output logic inj_o_done_ni_1755007830399_427,
    output logic inj_o_out_1755007830399_491,
    output logic inj_o_reg_out_1755007830402_621,
    output wire inj_o_wire_out_1755007830402_667,
    output logic [7:0] inj_out_nested_a_1755007830401_836,
    output logic [7:0] inj_out_nested_b_1755007830401_162,
    output bit [3:0] inj_out_status_1755007830401_118,
    output int inj_out_val_1755007830400_15,
    output logic [7:0] inj_out_val_1755007830400_984,
    output logic inj_result_1755007830400_491,
    output reg [15:0] inj_result_val_1755007830400_900,
    output logic inj_y_1755007830400_237
);
    // BEGIN: mod_no_inline_module_ts1755007830399
    logic r_toggle = 1'b0;
    // BEGIN: mod_split_nested_ts1755007830402
    logic [7:0]  split_nested_var_ts1755007830401;
    logic [7:0] other_nested_var_ts1755007830401;
        // BEGIN: nets_alias_clocking_ts1755007830402
        wire  w_internal_ts1755007830402;
        logic r_internal_ts1755007830402;
        assign w_internal_ts1755007830402  = reset & inj_b_1755007830400_455;
        assign inj_o_wire_out_1755007830402_667  = w_internal_ts1755007830402;
        always_ff @(posedge clk) r_internal_ts1755007830402 <= inj_i_in_1755007830399_789;
        assign inj_o_reg_out_1755007830402_621 = r_internal_ts1755007830402;
        // END: nets_alias_clocking_ts1755007830402

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var_ts1755007830401 <= 8'b0;
            other_nested_var_ts1755007830401 <= 8'b0;
        end else begin
            split_nested_var_ts1755007830401 <= 8'h11; 
            other_nested_var_ts1755007830401 <= 8'h22; 
            if (inj_data0_1755007830400_349) begin
                split_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 + 10;
                other_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 + 20;
                if (inj_b_1755007830400_455) begin
                    split_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 + 100;
                    other_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 + 200;
                end
            end else begin
                split_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 - 10;
                other_nested_var_ts1755007830401 <= inj_in_val_1755007830400_140 - 20;
            end
        end
    end
    always_comb begin
        inj_out_nested_a_1755007830401_836 = split_nested_var_ts1755007830401;
        inj_out_nested_b_1755007830401_162 = other_nested_var_ts1755007830401;
    end
    // END: mod_split_nested_ts1755007830402

    mod_case_standard mod_case_standard_inst_1755007830401_3870 (
        .out_status(inj_out_status_1755007830401_118),
        .in_cmd(inj_in_cmd_1755007830401_167)
    );
    nested_module nested_module_inst_1755007830401_484 (
        .nm_out(inj_nm_out_1755007830401_632),
        .nm_in(inj_data0_1755007830400_349)
    );
    // BEGIN: case_priority_overlapping_mod_ts1755007830400
    always @* begin
        priority casez (inj_case_expr_1755007830400_206)
            2'b1?: inj_internal_out_1755007830400_737 = 5;
            2'b?1: inj_internal_out_1755007830400_737 = 6;  
            2'b0?: inj_internal_out_1755007830400_737 = 7;
            2'b?0: inj_internal_out_1755007830400_737 = 8;  
            default: inj_internal_out_1755007830400_737 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007830400

    // BEGIN: recursive_param_diag_mod_ts1755007830400
    assign inj_out_val_1755007830400_15 = inj_dummy_in_1755007830400_396;
    // END: recursive_param_diag_mod_ts1755007830400

    generic_class_scope_diag_mod generic_class_scope_diag_mod_inst_1755007830400_2782 (
        .in_val(inj_in_val_1755007830400_140),
        .out_val(inj_out_val_1755007830400_984)
    );
    Comb_IfElse Comb_IfElse_inst_1755007830400_7063 (
        .value1(inj_value1_1755007830400_88),
        .value2(inj_value2_1755007830400_369),
        .result_val(inj_result_val_1755007830400_900),
        .condition(reset)
    );
    // BEGIN: multiplexer_2to1_ts1755007830400
    assign inj_result_1755007830400_491 = inj_i_in_1755007830399_789 ? inj_b_1755007830400_455 : inj_data0_1755007830400_349;
    // END: multiplexer_2to1_ts1755007830400

    // BEGIN: mod_comb_logic_ts1755007830400
    always_comb begin
        inj_y_1755007830400_237 = inj_i_in_1755007830399_789 & inj_b_1755007830400_455;
    end
    // END: mod_comb_logic_ts1755007830400

    // BEGIN: configuration_top_ts1755007830399
    assign inj_o_out_1755007830399_491 = inj_i_in_1755007830399_789;
    // END: configuration_top_ts1755007830399

    always_ff @(posedge reset) begin
        r_toggle <= ~r_toggle;
    end
    assign inj_o_done_ni_1755007830399_427 = r_toggle;
    // END: mod_no_inline_module_ts1755007830399
endmodule

