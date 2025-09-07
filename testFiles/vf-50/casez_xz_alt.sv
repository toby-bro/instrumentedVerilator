module formatting_stress (
    input logic [1:0] case_sel_fmt,
    input logic [7:0] data_in_fmt,
    input logic enable_block_fmt,
    input logic sel_fmt,
    output logic [7:0] data_out_fmt
);
    logic [7:0] temp_reg_fmt; 
    always_comb begin : stress_comb_block_label 
        data_out_fmt = 8'hXX; 
        if (enable_block_fmt) begin
            if (sel_fmt) begin
                case (case_sel_fmt) 
                    2'b00: data_out_fmt = data_in_fmt;
                    2'b01: begin 
                        data_out_fmt = ~data_in_fmt; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val; 
                        added_val = data_in_fmt + 8'h01; 
                        data_out_fmt = added_val; 
                        end 
                    default: data_out_fmt = 8'hFF; 
                endcase 
            end else begin
                data_out_fmt = data_in_fmt - 8'h01; 
            end 
        end else begin
            data_out_fmt = 8'h00; 
        end 
    end
endmodule

module casez_xz_alt (
    input wire clk,
    input logic [2:0] in_val,
    input logic [7:0] inj_data_in_k_1755538516317_891,
    input logic inj_in_1755538516316_557,
    input logic [7:0] inj_in_b_g_1755538516317_225,
    input logic [1:0] inj_in_val_1755538516318_649,
    input logic inj_sel_fmt_1755538516318_821,
    input wire rst,
    output logic [7:0] inj_data_out_fmt_1755538516318_941,
    output logic [7:0] inj_data_out_k_1755538516317_986,
    output logic [7:0] inj_out1_dd_1755538516317_674,
    output logic [7:0] inj_out2_dd_1755538516317_678,
    output logic inj_out_1755538516316_46,
    output logic [7:0] inj_out_p_g_1755538516317_278,
    output logic [7:0] inj_out_q_g_1755538516317_114,
    output reg inj_out_res_1755538516318_798,
    output reg out_res
);
    // BEGIN: mod_always_event_ts1755538516317
    // BEGIN: split_input_only_var_ts1755538516317
    // BEGIN: split_reorder_blocking_ts1755538516317
    logic [7:0] mid_x_g_ts1755538516317;
    logic [7:0] mid_y_g_ts1755538516317;
        formatting_stress formatting_stress_inst_1755538516318_7740 (
            .case_sel_fmt(inj_in_val_1755538516318_649),
            .data_in_fmt(inj_data_in_k_1755538516317_891),
            .enable_block_fmt(inj_in_1755538516316_557),
            .sel_fmt(inj_sel_fmt_1755538516318_821),
            .data_out_fmt(inj_data_out_fmt_1755538516318_941)
        );
        // BEGIN: case_basic_ts1755538516318
        always_comb begin
            inj_out_res_1755538516318_798 = 1'b0;
            case (inj_in_val_1755538516318_649)
                2'b00: inj_out_res_1755538516318_798 = 1'b0;
                2'b01: inj_out_res_1755538516318_798 = 1'b1;
                2'b10: inj_out_res_1755538516318_798 = 1'b0;
                2'b11: inj_out_res_1755538516318_798 = 1'b1;
            endcase
        end
        // END: case_basic_ts1755538516318

        // BEGIN: split_multi_nb_in_if_ts1755538516317
        always @(posedge clk) begin
            if (inj_in_1755538516316_557) begin
                inj_out1_dd_1755538516317_674 <= inj_data_in_k_1755538516317_891 + mid_y_g_ts1755538516317;
                inj_out2_dd_1755538516317_678 <= inj_in_b_g_1755538516317_225 - mid_x_g_ts1755538516317;
            end else begin
                inj_out1_dd_1755538516317_674 <= inj_data_in_k_1755538516317_891 * mid_y_g_ts1755538516317;
                inj_out2_dd_1755538516317_678 <= inj_in_b_g_1755538516317_225 / (mid_x_g_ts1755538516317 + 1);
            end
        end
        // END: split_multi_nb_in_if_ts1755538516317

    always @(*) begin
        mid_x_g_ts1755538516317 = inj_data_in_k_1755538516317_891 * 2;
        mid_y_g_ts1755538516317 = mid_x_g_ts1755538516317 + inj_in_b_g_1755538516317_225;
        inj_out_p_g_1755538516317_278 = mid_y_g_ts1755538516317 - 1;
        inj_out_q_g_1755538516317_114 = mid_x_g_ts1755538516317 / 2;
    end
    // END: split_reorder_blocking_ts1755538516317

    always @(posedge clk) begin
        if (inj_in_1755538516316_557) begin
            inj_data_out_k_1755538516317_986 <= inj_data_in_k_1755538516317_891;
        end
    end
    // END: split_input_only_var_ts1755538516317

    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            inj_out_1755538516316_46 <= 1'b0;
        end else begin
            inj_out_1755538516316_46 <= inj_in_1755538516316_557;
        end
    end
    // END: mod_always_event_ts1755538516317

    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

