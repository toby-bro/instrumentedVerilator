module snippet (
    input wire clk,
    input logic inj_condition_z_1755007897103_47,
    input logic [7:0] inj_d2_w_1755007897104_918,
    input logic [7:0] inj_d3_w_1755007897104_529,
    input logic [7:0] inj_in1_z_1755007897103_569,
    input logic [7:0] inj_in2_z_1755007897103_795,
    input int inj_in_val_1755007897104_812,
    input logic [1:0] inj_sel_w_1755007897104_47,
    input wire reset,
    output logic [7:0] inj_out1_z_1755007897103_870,
    output logic [7:0] inj_out2_z_1755007897103_388,
    output logic inj_out_o_1755007897103_575,
    output int inj_out_val_1755007897104_962,
    output logic [7:0] inj_out_w_1755007897104_468
);
    // BEGIN: mod_internal_if_test_ts1755007897103
    // BEGIN: split_diff_vars_branches_ts1755007897104
    // BEGIN: split_case_ts1755007897104
    // BEGIN: module_in_program_ref_ts1755007897104
    assign inj_out_val_1755007897104_962 = inj_in_val_1755007897104_812;
    // END: module_in_program_ref_ts1755007897104

    always @(posedge clk) begin
        case (inj_sel_w_1755007897104_47)
            2'b00: inj_out_w_1755007897104_468 <= inj_in1_z_1755007897103_569;
            2'b01: inj_out_w_1755007897104_468 <= inj_in2_z_1755007897103_795;
            2'b10: inj_out_w_1755007897104_468 <= inj_d2_w_1755007897104_918;
            default: inj_out_w_1755007897104_468 <= inj_d3_w_1755007897104_529;
        endcase
    end
    // END: split_case_ts1755007897104

    always @(posedge clk) begin
        if (inj_condition_z_1755007897103_47) begin
            inj_out1_z_1755007897103_870 <= inj_in1_z_1755007897103_569;
        end else begin
            inj_out2_z_1755007897103_388 <= inj_in2_z_1755007897103_795;
        end
    end
    // END: split_diff_vars_branches_ts1755007897104

    assign inj_out_o_1755007897103_575 = !clk;
    // END: mod_internal_if_test_ts1755007897103
endmodule

