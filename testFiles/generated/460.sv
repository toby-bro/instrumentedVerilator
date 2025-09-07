interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module simple_undeclared_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_1755007907943_527,
    input logic [15:0] inj_data_in_1755007907943_134,
    input int inj_in_val_1755007907943_66,
    input logic [7:0] inj_input_bf_1755007907944_961,
    input logic [3:0] inj_input_bf_slice_1755007907944_859,
    input wire reset,
    output logic inj_control_status_1755007907943_372,
    output logic [7:0] inj_out_q_1755007907944_879,
    output int inj_out_val_1755007907943_998,
    output int inj_out_val_1755007907944_639,
    output logic [7:0] inj_output_bf_1755007907944_34,
    output logic [3:0] inj_output_bf_slice_1755007907944_112
);
    // BEGIN: module_conditional_write_ts1755007907943
    // BEGIN: module_bitfield_concat_ts1755007907944
    logic [7:0] my_bitfield_ts1755007907944 ;
        // BEGIN: split_single_stmt_ts1755007907944
        always @(*) begin
            inj_out_q_1755007907944_879 = my_bitfield_ts1755007907944 + 1;
        end
        // END: split_single_stmt_ts1755007907944

        module_in_program_ref module_in_program_ref_inst_1755007907944_7622 (
            .in_val(inj_in_val_1755007907943_66),
            .out_val(inj_out_val_1755007907944_639)
        );
    always_comb begin
        if (inj_input_bf_1755007907944_961[7]) begin
            my_bitfield_ts1755007907944 = inj_input_bf_1755007907944_961;
        end else begin
            my_bitfield_ts1755007907944 = {inj_input_bf_1755007907944_961[0], inj_input_bf_1755007907944_961[7:1]};
        end
        my_bitfield_ts1755007907944[3:0] = inj_input_bf_slice_1755007907944_859;
    end
    assign inj_output_bf_1755007907944_34 = my_bitfield_ts1755007907944;
    assign inj_output_bf_slice_1755007907944_112 = my_bitfield_ts1755007907944[3:0];
    // END: module_bitfield_concat_ts1755007907944

    cond_if cif_inst();
    always_comb begin
        if (inj_condition_1755007907943_527) begin
            cif_inst.control_reg = inj_data_in_1755007907943_134;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007907943_372 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007907943

    simple_undeclared_mod simple_undeclared_mod_inst_1755007907943_9903 (
        .in_val(inj_in_val_1755007907943_66),
        .out_val(inj_out_val_1755007907943_998)
    );
endmodule

