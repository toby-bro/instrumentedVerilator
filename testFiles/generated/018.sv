interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d0_w_1755007756324_941,
    input logic [7:0] inj_d1_w_1755007756324_632,
    input logic [7:0] inj_data_case_a_1755007756323_674,
    input logic [7:0] inj_data_case_b_1755007756323_979,
    input logic inj_in_a_1755007756325_239,
    input logic [1:0] inj_select_case_1755007756323_609,
    input wire reset,
    output logic inj_case_output_ready_1755007756323_560,
    output logic inj_out_a_1755007756325_300,
    output logic [7:0] inj_out_w_1755007756324_867
);
    // BEGIN: module_case_write_ts1755007756323
    // BEGIN: split_case_ts1755007756324
    mod_name_conflict mod_name_conflict_inst_1755007756325_8400 (
        .in_a(inj_in_a_1755007756325_239),
        .out_a(inj_out_a_1755007756325_300)
    );
    always @(posedge clk) begin
        case (inj_select_case_1755007756323_609)
            2'b00: inj_out_w_1755007756324_867 <= inj_d0_w_1755007756324_941;
            2'b01: inj_out_w_1755007756324_867 <= inj_d1_w_1755007756324_632;
            2'b10: inj_out_w_1755007756324_867 <= inj_data_case_b_1755007756323_979;
            default: inj_out_w_1755007756324_867 <= inj_data_case_a_1755007756323_674;
        endcase
    end
    // END: split_case_ts1755007756324

    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755007756323_609)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = inj_data_case_a_1755007756323_674;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755007756323_979;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755007756323_560 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755007756323
endmodule

