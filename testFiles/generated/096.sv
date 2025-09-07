module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module snippet #(
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input logic [3:0] inj_data_in_1755007784624_144,
    input logic [15:0] inj_data_in_1755007784627_167,
    input bit [3:0] inj_in_data_1755007784626_265,
    input logic inj_nm_in_1755007784626_635,
    input int inj_sel_in_1755007784624_981,
    input wire reset,
    output logic [7:0] inj_data_out_1755007784624_189,
    output logic [15:0] inj_data_out_1755007784627_331,
    output logic inj_nm_out_1755007784626_788,
    output bit [3:0] inj_out_result_1755007784626_95
);
    // BEGIN: ModuleHierarchy_High_ts1755007784625
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (inj_sel_in_1755007784624_981),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007784625;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data_ts1755007784625)
        );
    end else begin : gen_low
        int low_data_ts1755007784625;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data_ts1755007784625)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007784625;
        assign sub_in_ts1755007784625 = inj_data_in_1755007784624_144[i*2 +: 2];
        int temp_int_ts1755007784625;
            // BEGIN: SequentialLogicPlaceholder_ts1755007784627
            always_ff @(posedge clk or posedge reset) begin
                if (reset) begin
                    inj_data_out_1755007784627_331 <= 16'h0;
                end else begin
                    inj_data_out_1755007784627_331 <= inj_data_in_1755007784627_167;
                end
            end
            // END: SequentialLogicPlaceholder_ts1755007784627

            // BEGIN: nested_module_ts1755007784626
            assign inj_nm_out_1755007784626_788 = inj_nm_in_1755007784626_635;
            // END: nested_module_ts1755007784626

            // BEGIN: mod_if_else_simple_ts1755007784626
        always_comb begin
            if (inj_in_data_1755007784626_265 > 8) begin
                inj_out_result_1755007784626_95 = inj_in_data_1755007784626_265 + 1;
            end else begin
                inj_out_result_1755007784626_95 = inj_in_data_1755007784626_265 - 1;
            end
        end
            // END: mod_if_else_simple_ts1755007784626

        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007784625)),
            .out_a  (),
            .out_b  (temp_int_ts1755007784625)
        );
        assign inj_data_out_1755007784624_189[i*4 +: 4] = temp_int_ts1755007784625[3:0];
    end
    // END: ModuleHierarchy_High_ts1755007784625
endmodule

