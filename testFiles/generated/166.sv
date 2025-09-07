module cu_base (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    assign data_out = data_in;
endmodule

module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
    typedef struct packed {
        logic [3:0] part1;
        logic [7:0] part2;
        logic [3:0] part3;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_data;
    assign unpacked_data = i_packed_data;
    always @* begin
        o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
    end
endmodule

module snippet (
    input wire clk,
    input wire inj_g_ctrl_n_1755007808751_751,
    input wire [15:0] inj_i_packed_data_1755007808751_601,
    input logic [7:0] inj_in_val_1755007808751_393,
    input wire reset,
    output logic [7:0] inj_data_out_1755007808751_84,
    output wire inj_g_out_and_1755007808751_264,
    output wire inj_g_out_or_1755007808751_343,
    output logic [7:0] inj_o_member_sum_1755007808751_105,
    output logic [7:0] inj_out_val_1755007808751_188
);
    // BEGIN: Module_GatePrimitives_ts1755007808751
    // BEGIN: generic_class_scope_diag_mod_ts1755007808751
    cu_base cu_base_inst_1755007808751_9904 (
        .data_out(inj_data_out_1755007808751_84),
        .data_in(inj_in_val_1755007808751_393)
    );
    assign inj_out_val_1755007808751_188 = inj_in_val_1755007808751_393;
    // END: generic_class_scope_diag_mod_ts1755007808751

    module_struct module_struct_inst_1755007808751_6407 (
        .i_packed_data(inj_i_packed_data_1755007808751_601),
        .o_member_sum(inj_o_member_sum_1755007808751_105)
    );
    and a1 (inj_g_out_and_1755007808751_264, reset, reset);
    or  o1 (inj_g_out_or_1755007808751_343 , reset, reset);
    // END: Module_GatePrimitives_ts1755007808751
endmodule

