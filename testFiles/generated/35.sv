module expr_postsub_comb (
    input logic [7:0] in_val_m2,
    input logic [7:0] sub_val_m2,
    output logic [7:0] out_diff_m2,
    output logic [7:0] var_out_m2
);
    logic [7:0] var_m2;
    always_comb begin
        var_m2 = in_val_m2;
        out_diff_m2 = (var_m2--) - sub_val_m2;
        var_out_m2 = var_m2;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_val_m2_1755004214967_773,
    input logic [7:0] inj_sub_val_m2_1755004214967_564,
    input wire reset,
    output logic [7:0] inj_out_diff_m2_1755004214967_333,
    output logic [7:0] inj_var_out_m2_1755004214967_145
);
    expr_postsub_comb expr_postsub_comb_inst_1755004214967_8534 (
        .out_diff_m2(inj_out_diff_m2_1755004214967_333),
        .var_out_m2(inj_var_out_m2_1755004214967_145),
        .in_val_m2(inj_in_val_m2_1755004214967_773),
        .sub_val_m2(inj_sub_val_m2_1755004214967_564)
    );
endmodule

