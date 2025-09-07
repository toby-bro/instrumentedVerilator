module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [7:0] inj_data_in_1755007899267_103,
    input logic inj_enable_1755007899267_752,
    input integer inj_in_int_1755007899269_372,
    input logic [31:0] inj_in_l32_1755007899269_778,
    input logic [15:0] inj_in_u16_1755007899269_315,
    input logic [2:0] inj_sel_in_1755007899268_318,
    input wire reset,
    output reg [7:0] inj_data_out_1755007899268_752,
    output logic [7:0] inj_dout_1755007899270_927,
    output logic inj_o_attr_out_1755007899273_328,
    output logic [7:0] inj_out_a_1755007899267_282,
    output logic [7:0] inj_out_b_1755007899267_842,
    output reg inj_out_res_1755007899271_153,
    output logic signed [15:0] inj_out_s16_1755007899269_710,
    output logic signed [31:0] inj_out_s32_from_int_1755007899269_717,
    output logic signed [31:0] inj_out_s32_from_l32_1755007899269_762,
    output logic [7:0] inj_out_sum_1755007899268_568,
    output logic [31:0] inj_out_u32_from_int_1755007899269_220,
    output logic [31:0] inj_out_u32_from_l32_1755007899269_183,
    output logic [7:0] inj_out_u8_1755007899269_779
);
    // BEGIN: mod_split_comb_ts1755007899268
    logic [7:0]  split_comb_var_ts1755007899268;
    logic [7:0] other_comb_var_ts1755007899268;
        // BEGIN: simple_for_loop_ts1755007899269
        logic [7:0] sum_ts1755007899268;
            // BEGIN: attributes_test_ts1755007899273
            (* synthesis_preserve *) logic internal_signal;
            always_comb begin : my_combinational_block
                internal_signal = inj_enable_1755007899267_752 ? 1'b1 : 1'b0;
                inj_o_attr_out_1755007899273_328      = internal_signal;
            end
            // END: attributes_test_ts1755007899273

            // BEGIN: casez_xz_alt_ts1755007899272
            always_comb begin
                inj_out_res_1755007899271_153 = 1'b0;
                casez (inj_sel_in_1755007899268_318)
                    3'b1?z: inj_out_res_1755007899271_153 = 1'b1;
                    3'b0z?: inj_out_res_1755007899271_153 = 1'b0;
                    default: inj_out_res_1755007899271_153 = 1'b1;
                endcase
            end
            // END: casez_xz_alt_ts1755007899272

            // BEGIN: Parameterized_ts1755007899270
            assign inj_dout_1755007899270_927 = sum_ts1755007899268;
            // END: Parameterized_ts1755007899270

            // BEGIN: SignedUnsignedConversions_ts1755007899270
            always_comb begin
                inj_out_u8_1755007899269_779 = $unsigned(other_comb_var_ts1755007899268);
                inj_out_s16_1755007899269_710 = $signed(inj_in_u16_1755007899269_315);
                inj_out_s32_from_l32_1755007899269_762 = $signed(inj_in_l32_1755007899269_778);
                inj_out_u32_from_l32_1755007899269_183 = $unsigned(inj_in_l32_1755007899269_778);
                inj_out_s32_from_int_1755007899269_717 = $signed(inj_in_int_1755007899269_372);
                inj_out_u32_from_int_1755007899269_220 = $unsigned(inj_in_int_1755007899269_372);
            end
            // END: SignedUnsignedConversions_ts1755007899270

        always_comb begin
            sum_ts1755007899268 = 8'h00;
            for (int i = 0; i < 5; i = i + 1) begin
                sum_ts1755007899268 = sum_ts1755007899268 + split_comb_var_ts1755007899268;
            end
            inj_out_sum_1755007899268_568 = sum_ts1755007899268;
        end
        // END: simple_for_loop_ts1755007899269

        Module_ControlFlow Module_ControlFlow_inst_1755007899268_8880 (
            .sel_in(inj_sel_in_1755007899268_318),
            .data_out(inj_data_out_1755007899268_752),
            .clk(clk),
            .data_in(inj_data_in_1755007899267_103),
            .reset_n(reset)
        );
    always_comb begin
        split_comb_var_ts1755007899268 = 8'b0; 
        other_comb_var_ts1755007899268 = 8'b0;
        if (inj_enable_1755007899267_752) begin
            split_comb_var_ts1755007899268 = inj_data_in_1755007899267_103;
            other_comb_var_ts1755007899268 = inj_data_in_1755007899267_103 + 1;
        end
        inj_out_a_1755007899267_282 = split_comb_var_ts1755007899268;
        inj_out_b_1755007899267_842 = other_comb_var_ts1755007899268;
    end
    // END: mod_split_comb_ts1755007899268
endmodule

