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

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic inj_c1_x_1755007812092_631,
    input logic inj_c2_x_1755007812092_73,
    input logic [3:0] inj_data_in_1755007812093_387,
    input logic inj_in_a_1755007812092_419,
    input logic [7:0] inj_in_a_1755007812092_579,
    input logic [7:0] inj_in_b_1755007812092_611,
    input int inj_sel_in_1755007812093_620,
    input logic [7:0] inj_v2_x_1755007812092_854,
    input logic [7:0] inj_v4_x_1755007812092_654,
    input wire reset,
    output logic [7:0] inj_data_out_1755007812093_32,
    output logic inj_out_a_1755007812092_845,
    output logic [15:0] inj_out_concat_1755007812092_941,
    output logic [7:0] inj_out_x_1755007812092_404
);
    // BEGIN: ComplexConversions_ts1755007812092
    // BEGIN: split_ifelse_chain_ts1755007812093
    // BEGIN: ModuleHierarchy_Low_ts1755007812094
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (inj_sel_in_1755007812093_620),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007812094;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data_ts1755007812094)
        );
    end else begin : gen_low
        int low_data_ts1755007812094;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data_ts1755007812094)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007812094;
        assign sub_in_ts1755007812094 = inj_data_in_1755007812093_387[i*2 +: 2];
        int temp_int_ts1755007812094;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007812094)),
            .out_a  (),
            .out_b  (temp_int_ts1755007812094)
        );
        assign inj_data_out_1755007812093_32[i*4 +: 4] = temp_int_ts1755007812094[3:0];
    end
    // END: ModuleHierarchy_Low_ts1755007812094

    always @(posedge clk) begin
        if (inj_c1_x_1755007812092_631) begin
            inj_out_x_1755007812092_404 <= inj_in_a_1755007812092_579;
        end else if (inj_c2_x_1755007812092_73) begin
            inj_out_x_1755007812092_404 <= inj_v2_x_1755007812092_854;
        end else if (inj_in_a_1755007812092_419) begin
            inj_out_x_1755007812092_404 <= inj_in_b_1755007812092_611;
        end else begin
            inj_out_x_1755007812092_404 <= inj_v4_x_1755007812092_654;
        end
    end
    // END: split_ifelse_chain_ts1755007812093

    always_comb begin
        inj_out_concat_1755007812092_941 = {inj_in_a_1755007812092_579, inj_in_b_1755007812092_611};
    end
    // END: ComplexConversions_ts1755007812092

    mod_name_conflict mod_name_conflict_inst_1755007812092_6222 (
        .in_a(inj_in_a_1755007812092_419),
        .out_a(inj_out_a_1755007812092_845)
    );
endmodule

