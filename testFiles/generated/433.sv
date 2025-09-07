module snippet (
    input wire clk,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007898959_55,
    input wire [15:0] inj_dffcl_data_in1_1755007898959_403,
    input wire [15:0] inj_dffcl_data_in2_1755007898959_14,
    input wire reset,
    output logic [15:0] inj_dffcl_data_out_1755007898959_779
);
    // BEGIN: deep_ff_control_logic_ts1755007898960
    always_ff @(posedge clk or negedge reset) begin
    if (!reset) begin
        inj_dffcl_data_out_1755007898959_779 <= 16'h0000;
    end else begin
        case (inj_dffcl_ctrl_mode_1755007898959_55)
            4'd0: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 + inj_dffcl_data_in2_1755007898959_14;
            4'd1: begin
                if (inj_dffcl_data_in1_1755007898959_403 > inj_dffcl_data_in2_1755007898959_14) begin
                    case (inj_dffcl_ctrl_mode_1755007898959_55[1:0])
                        2'b00: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 - inj_dffcl_data_in2_1755007898959_14;
                        2'b01: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 & inj_dffcl_data_in2_1755007898959_14;
                        default: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 | inj_dffcl_data_in2_1755007898959_14;
                    endcase
                end else begin
                    case (inj_dffcl_ctrl_mode_1755007898959_55[1:0])
                        2'b00: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in2_1755007898959_14 - inj_dffcl_data_in1_1755007898959_403;
                        2'b01: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 ^ inj_dffcl_data_in2_1755007898959_14;
                        default: inj_dffcl_data_out_1755007898959_779 <= ~inj_dffcl_data_in1_1755007898959_403;
                    endcase
                end
            end
            4'd2: begin
                casez (inj_dffcl_data_in1_1755007898959_403[15:13])
                    3'b000: inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in2_1755007898959_14;
                    3'b001: inj_dffcl_data_out_1755007898959_779 <= ~inj_dffcl_data_in2_1755007898959_14;
                    3'b01?: begin
                        if (inj_dffcl_data_in2_1755007898959_14[0]) inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 << 1;
                        else inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 >> 1;
                    end
                    3'b1??: begin
                        if (inj_dffcl_ctrl_mode_1755007898959_55[0]) inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 + 1;
                        else inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403 - 1;
                    end
                    default: inj_dffcl_data_out_1755007898959_779 <= 16'hAAAA;
                endcase
            end
            default: begin
                if (inj_dffcl_ctrl_mode_1755007898959_55[2]) inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in1_1755007898959_403;
                else inj_dffcl_data_out_1755007898959_779 <= inj_dffcl_data_in2_1755007898959_14;
            end
        endcase
    end
    end
    // END: deep_ff_control_logic_ts1755007898960
endmodule

