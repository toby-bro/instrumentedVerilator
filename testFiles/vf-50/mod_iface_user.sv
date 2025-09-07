interface my_interface #(
    parameter int WIDTH = 8
) (
    input logic clk,
    output logic [7:0] data
);
    logic [WIDTH-1:0] internal_data;
    modport mp (
        input clk,
        output data
    );
    assign data = internal_data;
endinterface
module mod_iface_user (
    input logic i_clk,
    input logic inj_a_1755538392856_720,
    input int inj_data_in_1755538392856_698,
    input wire rst,
    output logic [7:0] i_data,
    output int inj_data_out_1755538392856_292,
    output int inj_out_val_1755538392856_929,
    output logic inj_y_1755538392856_675
);
    // BEGIN: mod_named_begin_ts1755538392856
    // BEGIN: ModSimpleLogic_ts1755538392856
    // BEGIN: local_not_allowed_diag_mod_ts1755538392856
    assign inj_out_val_1755538392856_929 = inj_data_in_1755538392856_698;
    // END: local_not_allowed_diag_mod_ts1755538392856

    assign inj_y_1755538392856_675 = inj_a_1755538392856_720 ^ i_clk;
    // END: ModSimpleLogic_ts1755538392856

    always_comb begin : my_named_block
        inj_data_out_1755538392856_292 = inj_data_in_1755538392856_698;
    end
    // END: mod_named_begin_ts1755538392856

    my_interface #(.WIDTH(8)) iface_inst (.clk(i_clk), .data(i_data));
endmodule

