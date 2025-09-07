interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module snippet (
    input wire clk,
    input logic [7:0] inj_addr_1755007893050_289,
    input logic [1:0] inj_case_expr_1755007893050_57,
    input logic [7:0] inj_wdata_1755007893050_719,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007893050_810,
    output logic inj_write_status_1755007893050_688
);
    // BEGIN: case_full_simple_mod_ts1755007893050
    // BEGIN: module_sequential_writes_ts1755007893050
    my_if vif_bus();
    always_comb begin
        vif_bus.data = inj_wdata_1755007893050_719;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        inj_write_status_1755007893050_688 = vif_bus.ready;
    end
    // END: module_sequential_writes_ts1755007893050

    always @* begin
        (* full *)
        case (inj_case_expr_1755007893050_57)
            2'b00: inj_internal_out_1755007893050_810 = 10;
            2'b01: inj_internal_out_1755007893050_810 = 11;
            2'b10: inj_internal_out_1755007893050_810 = 12;
            default: inj_internal_out_1755007893050_810 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755007893050
endmodule

