module top_module_config_dummy (
    input logic i,
    output logic o
);
    assign o = i; 
endmodule

module snippet (
    input wire clk,
    input logic inj_i_1755007797215_934,
    input logic [1:0] inj_in_val_1755007797215_638,
    input wire reset,
    output wire inj_match_x_neq_1755007797216_766,
    output wire inj_match_z_eq_1755007797216_802,
    output logic inj_o_1755007797215_349,
    output reg inj_out_res_1755007797215_891,
    output reg inj_out_res_1755007797216_128,
    inout wire [3:0] inj_data_io_1755007797216_593
);
    // BEGIN: case_basic_ts1755007797215
    // BEGIN: case_basic_ts1755007797216
    // BEGIN: CaseEq_ts1755007797216
    assign inj_match_z_eq_1755007797216_802 = (inj_data_io_1755007797216_593 === 4'b101z);
    assign inj_match_x_neq_1755007797216_766 = (inj_data_io_1755007797216_593 !== 4'b1x0x);
    // END: CaseEq_ts1755007797216

    always_comb begin
        inj_out_res_1755007797216_128 = 1'b0;
        case (inj_in_val_1755007797215_638)
            2'b00: inj_out_res_1755007797216_128 = 1'b0;
            2'b01: inj_out_res_1755007797216_128 = 1'b1;
            2'b10: inj_out_res_1755007797216_128 = 1'b0;
            2'b11: inj_out_res_1755007797216_128 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007797216

    always_comb begin
        inj_out_res_1755007797215_891 = 1'b0;
        case (inj_in_val_1755007797215_638)
            2'b00: inj_out_res_1755007797215_891 = 1'b0;
            2'b01: inj_out_res_1755007797215_891 = 1'b1;
            2'b10: inj_out_res_1755007797215_891 = 1'b0;
            2'b11: inj_out_res_1755007797215_891 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007797215

    top_module_config_dummy top_module_config_dummy_inst_1755007797215_9990 (
        .i(inj_i_1755007797215_934),
        .o(inj_o_1755007797215_349)
    );
endmodule

