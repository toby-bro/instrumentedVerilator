module ModuleGenerateIf (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val = in_val + 10;
        end else begin : bypass_block
            assign processed_val = in_val;
        end
    endgenerate
    assign out_val = processed_val;
endmodule

module snippet (
    input wire clk,
    input int inj_data_in_1755007873936_753,
    input logic [7:0] inj_in_val_1755007873936_329,
    input wire reset,
    output int inj_data_out_1755007873936_448,
    output wire inj_out_1755007873936_998,
    output logic [7:0] inj_out_val_1755007873936_301
);
    // BEGIN: mod_named_begin_ts1755007873936
    // BEGIN: Comb_Assign_ts1755007873936
    assign inj_out_1755007873936_998 = clk & reset;
    // END: Comb_Assign_ts1755007873936

    always_comb begin : my_named_block
        inj_data_out_1755007873936_448 = inj_data_in_1755007873936_753;
    end
    // END: mod_named_begin_ts1755007873936

    ModuleGenerateIf ModuleGenerateIf_inst_1755007873936_1219 (
        .in_val(inj_in_val_1755007873936_329),
        .out_val(inj_out_val_1755007873936_301)
    );
endmodule

