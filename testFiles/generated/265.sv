module mod_simple_ref (
    input logic i_data,
    output logic o_result
);
    logic internal_sig;
    always_comb begin
        internal_sig = i_data;
        o_result = internal_sig;
    end
endmodule

module name_conflict_example (
    input logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007843068_392,
    input logic inj_dummy_in_1755007843068_145,
    input logic [1:0] inj_in_val_1755007843068_8,
    input wire reset,
    output logic inj_dummy_out_1755007843068_126,
    output logic inj_o_out_1755007843069_30,
    output logic inj_o_result_1755007843069_593,
    output reg inj_out_res_1755007843068_859
);
    // BEGIN: case_empty_statement_ts1755007843068
    // BEGIN: mixed_conn_child_ts1755007843068
    logic dummy_internal_ts1755007843068;
        name_conflict_example name_conflict_example_inst_1755007843069_1578 (
            .i_in(inj_dummy_in_1755007843068_145),
            .o_out(inj_o_out_1755007843069_30)
        );
        mod_simple_ref mod_simple_ref_inst_1755007843069_5588 (
            .i_data(inj_dummy_in_1755007843068_145),
            .o_result(inj_o_result_1755007843069_593)
        );
    always_comb dummy_internal_ts1755007843068 = |inj_data_in_1755007843068_392 | inj_dummy_in_1755007843068_145;
    assign inj_dummy_out_1755007843068_126 = dummy_internal_ts1755007843068;
    // END: mixed_conn_child_ts1755007843068

    always_comb begin
        inj_out_res_1755007843068_859 = 1'b0;
        case (inj_in_val_1755007843068_8)
            2'b00: inj_out_res_1755007843068_859 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007843068_859 = 1'b0;
            default: inj_out_res_1755007843068_859 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007843068
endmodule

