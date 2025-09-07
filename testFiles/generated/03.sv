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
    input logic [7:0] inj_in_data_1755004203463_257,
    input wire reset,
    output logic inj_out_valid_status_1755004203463_829
);
    // BEGIN: module_assign_blocking_ts1755004203464
    my_if vif_inst();
    always_comb begin
        vif_inst.data = inj_in_data_1755004203463_257;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        inj_out_valid_status_1755004203463_829 = vif_inst.valid;
    end
    // END: module_assign_blocking_ts1755004203464
endmodule

