module Module_BasicSyntax (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic out_cmp,
    output logic [7:0] out_ops
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
endmodule

module SynchronousMemory (
    input logic clk,
    input logic [4:0] read_address,
    input logic rst,
    input logic [4:0] write_address,
    input logic [7:0] write_data,
    input logic write_en,
    output logic [7:0] read_data
);
    logic [7:0] mem [0:31];
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            read_data <= 8'h0;
        end else begin
            if (write_en) begin
                mem[write_address] <= write_data;
            end
            read_data <= mem[read_address];
        end
    end
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_c_1755007762045_244,
    input bit [3:0] inj_in1_1755007762043_848,
    input bit [3:0] inj_in2_1755007762043_555,
    input bit inj_in_1755007762043_934,
    input logic [7:0] inj_in_a_1755007762043_290,
    input logic [7:0] inj_in_b_1755007762043_925,
    input logic [2:0] inj_index_1755007762044_837,
    input logic [4:0] inj_read_address_1755007762043_776,
    input logic [4:0] inj_write_address_1755007762043_267,
    input logic inj_write_en_1755007762043_153,
    input wire reset,
    output logic inj_anded_1755007762045_784,
    output logic inj_diff_1755007762045_355,
    output logic inj_o_out_1755007762044_783,
    output logic inj_ored_1755007762045_77,
    output bit [3:0] inj_out1_1755007762043_128,
    output bit [3:0] inj_out2_1755007762043_335,
    output bit inj_out_1755007762043_501,
    output logic inj_out_1755007762044_569,
    output logic inj_out_cmp_1755007762043_624,
    output logic [7:0] inj_out_ops_1755007762043_438,
    output logic [7:0] inj_read_data_1755007762043_838,
    output logic [7:0] inj_sum_1755007762045_668,
    output logic inj_xored_1755007762045_520
);
    // BEGIN: BindSimpleModule_ts1755007762043
    // BEGIN: ModuleFF_ts1755007762044
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg_ts1755007762044;
    integer unused_int_var_ts1755007762044;
        // BEGIN: name_conflict_example_ts1755007762044
        parameter int my_param = 5;
        logic my_var_ts1755007762044;
            // BEGIN: more_ops_ts1755007762045
            assign inj_sum_1755007762045_668 = inj_in_a_1755007762043_290 + inj_in_b_1755007762043_925;
            assign inj_diff_1755007762045_355 = inj_in_a_1755007762043_290 > inj_c_1755007762045_244;
            assign inj_anded_1755007762045_784 = inj_in_a_1755007762043_290 & inj_in_b_1755007762043_925;
            assign inj_ored_1755007762045_77 = inj_in_a_1755007762043_290 | inj_c_1755007762045_244;
            assign inj_xored_1755007762045_520 = inj_in_a_1755007762043_290 ^ inj_in_b_1755007762043_925;
            // END: more_ops_ts1755007762045

        always_comb my_var_ts1755007762044 = inj_write_en_1755007762043_153;
        assign inj_o_out_1755007762044_783 = inj_write_en_1755007762043_153 && (my_param == 5) && my_var_ts1755007762044;
        // END: name_conflict_example_ts1755007762044

        variable_sel_mux variable_sel_mux_inst_1755007762044_1207 (
            .in(inj_in_a_1755007762043_290),
            .index(inj_index_1755007762044_837),
            .out(inj_out_1755007762044_569)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg_ts1755007762044 <= START_VAL;
            inj_out1_1755007762043_128 <= '0;
            inj_out2_1755007762043_335 <= '0;
            unused_int_var_ts1755007762044 <= 0;
        end else begin
            case ({inj_in1_1755007762043_848, inj_in2_1755007762043_555})
                8'h00: ff_reg_ts1755007762044 <= ff_reg_ts1755007762044;
                8'h01: ff_reg_ts1755007762044 <= inj_in1_1755007762043_848 + inj_in2_1755007762043_555;
                default: ff_reg_ts1755007762044 <= MAX_COUNT;
            endcase
            inj_out1_1755007762043_128 <= ff_reg_ts1755007762044;
            inj_out2_1755007762043_335 <= {inj_in1_1755007762043_848[0], inj_in1_1755007762043_848[0], inj_in1_1755007762043_848[0], inj_in1_1755007762043_848[0]} | {inj_in2_1755007762043_555[3], inj_in2_1755007762043_555[2], inj_in2_1755007762043_555[1], inj_in2_1755007762043_555[0]};
        end
    end
    // END: ModuleFF_ts1755007762044

    SynchronousMemory SynchronousMemory_inst_1755007762043_9448 (
        .read_data(inj_read_data_1755007762043_838),
        .clk(clk),
        .read_address(inj_read_address_1755007762043_776),
        .rst(reset),
        .write_address(inj_write_address_1755007762043_267),
        .write_data(inj_in_a_1755007762043_290),
        .write_en(inj_write_en_1755007762043_153)
    );
    Module_BasicSyntax Module_BasicSyntax_inst_1755007762043_4376 (
        .out_ops(inj_out_ops_1755007762043_438),
        .in_a(inj_in_a_1755007762043_290),
        .in_b(inj_in_b_1755007762043_925),
        .out_cmp(inj_out_cmp_1755007762043_624)
    );
    assign inj_out_1755007762043_501 = inj_in_1755007762043_934;
    // END: BindSimpleModule_ts1755007762043
endmodule

