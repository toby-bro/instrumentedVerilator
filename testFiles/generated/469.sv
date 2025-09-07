module comb_conditional (
    input bit [7:0] data1,
    input bit [7:0] data2,
    input bit sel,
    output bit [7:0] result1,
    output bit [7:0] result2
);
    always @* begin
        if (sel) begin
            result1 = data1;
            result2 = data1;
        end else begin
            result1 = data2;
            result2 = data2;
        end
    end
endmodule

module macro_line_continuation_user (
    input logic lc_en,
    output logic [15:0] lc_val
);
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg;
    always_comb begin
        if (lc_en)
            value_reg = `MULTI_VAL;
        else
            value_reg = `ADD_FIVE(16'h0010);
    end
    assign lc_val = value_reg;
endmodule

module split_basic_blocking (
    input logic [7:0] in1_a,
    output logic [7:0] out1_a
);
    always @(*) begin
        out1_a = in1_a;
    end
endmodule

module snippet (
    input wire clk,
    input bit [7:0] inj_data1_1755007910961_964,
    input bit [7:0] inj_data2_1755007910961_116,
    input logic [7:0] inj_in1_a_1755007910960_230,
    input logic inj_lc_en_1755007910961_197,
    input bit inj_sel_1755007910961_787,
    input logic [1:0] inj_selector_1755007910960_321,
    input wire reset,
    output logic [7:0] inj_data_out_1755007910962_737,
    output logic [15:0] inj_lc_val_1755007910961_125,
    output logic [7:0] inj_out1_a_1755007910960_331,
    output bit [7:0] inj_result1_1755007910961_894,
    output bit [7:0] inj_result2_1755007910961_828,
    output logic [7:0] inj_selected_output_1755007910960_567
);
    // BEGIN: generate_for_block_ts1755007910961
    wire [7:0] data_ts1755007910961 [3:0]; 
        // BEGIN: cu_base_ts1755007910962
        assign inj_data_out_1755007910962_737 = inj_in1_a_1755007910960_230;
        // END: cu_base_ts1755007910962

        macro_line_continuation_user macro_line_continuation_user_inst_1755007910961_8959 (
            .lc_val(inj_lc_val_1755007910961_125),
            .lc_en(inj_lc_en_1755007910961_197)
        );
        comb_conditional comb_conditional_inst_1755007910961_5505 (
            .data1(inj_data1_1755007910961_964),
            .data2(inj_data2_1755007910961_116),
            .sel(inj_sel_1755007910961_787),
            .result1(inj_result1_1755007910961_894),
            .result2(inj_result2_1755007910961_828)
        );
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data_ts1755007910961[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (inj_selector_1755007910960_321)
            0: inj_selected_output_1755007910960_567 = data_ts1755007910961[0];
            1: inj_selected_output_1755007910960_567 = data_ts1755007910961[1];
            2: inj_selected_output_1755007910960_567 = data_ts1755007910961[2];
            3: inj_selected_output_1755007910960_567 = data_ts1755007910961[3];
            default: inj_selected_output_1755007910960_567 = 8'hXX;
        endcase
    end
    // END: generate_for_block_ts1755007910961

    split_basic_blocking split_basic_blocking_inst_1755007910960_3674 (
        .in1_a(inj_in1_a_1755007910960_230),
        .out1_a(inj_out1_a_1755007910960_331)
    );
endmodule

