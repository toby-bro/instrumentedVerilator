module snippet (
    input wire clk,
    input logic [2:0] inj_in1_1755004204747_420,
    input logic inj_in2_1755004204747_22,
    input logic [7:0] inj_in_val_1755004204747_188,
    input logic [31:0] inj_p_in1_1755004204747_594,
    input logic [31:0] inj_p_in2_1755004204747_912,
    input logic [1:0] inj_p_mode_1755004204747_147,
    input wire reset,
    output logic inj_extra_out_1755004204747_766,
    output logic inj_out1_1755004204747_871,
    output logic inj_out2_1755004204747_490,
    output logic [7:0] inj_out_val_1755004204747_55,
    output logic [31:0] inj_p_out_1755004204747_747
);
    // BEGIN: used_before_declared_diag_mod_ts1755004204747
    logic [7:0] undeclared_var_ubddm = 8'd5;
    // BEGIN: more_procedural_ts1755004204748
    always_comb begin
        case (inj_p_mode_1755004204747_147)
            2'b00: inj_p_out_1755004204747_747 = (inj_p_in1_1755004204747_594 + inj_p_in2_1755004204747_912) * 2;
            2'b01: inj_p_out_1755004204747_747 = (inj_p_in1_1755004204747_594 - inj_p_in2_1755004204747_912) / 3; 
            2'b10: inj_p_out_1755004204747_747 = (inj_p_in1_1755004204747_594 << 4) | (inj_p_in2_1755004204747_912 >> 2);
            default: inj_p_out_1755004204747_747 = ~(inj_p_in1_1755004204747_594 ^ inj_p_in2_1755004204747_912) + 1;
        endcase
    end
    // END: more_procedural_ts1755004204748

    // BEGIN: ansi_implicit_inherit_ts1755004204747
    always_comb begin
        inj_out1_1755004204747_871 = |inj_in1_1755004204747_420;
        inj_out2_1755004204747_490 = |inj_in2_1755004204747_22;
        inj_extra_out_1755004204747_766 = inj_out1_1755004204747_871 ^ inj_out2_1755004204747_490;
    end
    // END: ansi_implicit_inherit_ts1755004204747

    assign inj_out_val_1755004204747_55 = inj_in_val_1755004204747_188 + undeclared_var_ubddm;
    // END: used_before_declared_diag_mod_ts1755004204747
endmodule

