interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module snippet (
    input wire clk,
    input logic inj_condition_1755007828677_739,
    input logic [15:0] inj_data_in_1755007828677_109,
    input wire reset,
    output logic inj_control_status_1755007828677_466
);
    // BEGIN: module_conditional_write_ts1755007828677
    cond_if cif_inst();
    always_comb begin
        if (inj_condition_1755007828677_739) begin
            cif_inst.control_reg = inj_data_in_1755007828677_109;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007828677_466 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007828677
endmodule

