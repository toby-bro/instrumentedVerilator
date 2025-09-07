module snippet (
    input wire clk,
    input logic [1:0] inj_case_sel_fmt_1755007773534_0,
    input logic [7:0] inj_data_in_fmt_1755007773534_877,
    input logic inj_enable_block_fmt_1755007773534_307,
    input bit inj_enable_crypto_1755007773535_37,
    input logic inj_sel_fmt_1755007773534_865,
    input wire reset,
    output bit inj_crypto_active_1755007773535_436,
    output logic [7:0] inj_data_out_fmt_1755007773534_320,
    output logic inj_fs_out_target_1755007773535_748,
    output logic [7:0] inj_out_val_c_1755007773536_650
);
    // BEGIN: formatting_stress_ts1755007773535
    logic [7:0] temp_reg_fmt_ts1755007773535; 
    always_comb begin : stress_comb_block_label 
        inj_data_out_fmt_1755007773534_320 = 8'hXX; 
        if (inj_enable_block_fmt_1755007773534_307) begin
            if (inj_sel_fmt_1755007773534_865) begin
                case (inj_case_sel_fmt_1755007773534_0) 
                    2'b00: inj_data_out_fmt_1755007773534_320 = inj_data_in_fmt_1755007773534_877;
                    2'b01: begin 
                        inj_data_out_fmt_1755007773534_320 = ~inj_data_in_fmt_1755007773534_877; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val_ts1755007773535; 
                            // BEGIN: split_seq_dependency_ts1755007773536
                            logic [7:0] mid_val_c_ts1755007773536;
                            always @(posedge clk) begin
                                mid_val_c_ts1755007773536 <= temp_reg_fmt_ts1755007773535 + 1;
                                inj_out_val_c_1755007773536_650 <= mid_val_c_ts1755007773536 * 2;
                            end
                            // END: split_seq_dependency_ts1755007773536

                            // BEGIN: PragmaProtectKeyBlock_ts1755007773536
                        `ifdef SLANG_PRAGMA
                        `protect key
                        `endif
                        `ifdef SLANG_PRAGMA
                        `protect block
                        `endif
                        assign inj_crypto_active_1755007773535_436 = inj_enable_crypto_1755007773535_37;
                            // END: PragmaProtectKeyBlock_ts1755007773536

                            // BEGIN: mod_fixup_target_ts1755007773535
                            assign inj_fs_out_target_1755007773535_748 = inj_enable_block_fmt_1755007773534_307;
                            // END: mod_fixup_target_ts1755007773535

                        added_val_ts1755007773535 = inj_data_in_fmt_1755007773534_877 + 8'h01; 
                        inj_data_out_fmt_1755007773534_320 = added_val_ts1755007773535; 
                        end 
                    default: inj_data_out_fmt_1755007773534_320 = 8'hFF; 
                endcase 
            end else begin
                inj_data_out_fmt_1755007773534_320 = inj_data_in_fmt_1755007773534_877 - 8'h01; 
            end 
        end else begin
            inj_data_out_fmt_1755007773534_320 = 8'h00; 
        end 
    end
    // END: formatting_stress_ts1755007773535
endmodule

