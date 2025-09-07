interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module dup_cond (
    input logic [3:0] control,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result1,
    output logic [7:0] result2
);
    always_comb begin
        result1 = '0;
        result2 = '0;
        if (control[0]) begin
            result1 = data_a + data_b;
        end else begin
            result1 = data_a - data_b;
        end
        if (control[1]) begin
            result2 = data_a - data_b;
        end else begin
            result2 = data_a + data_b;
        end
        case (control[3:2])
            2'b00: result1 = data_a & data_b;
            2'b01: result1 = data_a | data_b;
            2'b10: result2 = data_a & data_b;
            2'b11: result2 = data_a | data_b;
            default: begin result1 = '0; result2 = '0; end
        endcase
        if (control[0] == control[1]) begin
            result1 = result1 + 1;
        end else if (control[2] != control[3]) begin
            result2 = result2 - 1;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_control_1755007827990_879,
    input logic inj_d_1755007827990_693,
    input logic [7:0] inj_data_a_1755007827990_6,
    input logic [7:0] inj_data_b_1755007827990_970,
    input logic [2:0] inj_in_val_1755007827990_724,
    input wire reset,
    output reg inj_out_res_1755007827990_548,
    output logic inj_q_1755007827990_150,
    output logic [7:0] inj_result1_1755007827990_829,
    output logic [7:0] inj_result2_1755007827990_9,
    output logic inj_task_output_valid_1755007827990_731
);
    // BEGIN: mod_seq_reg_ts1755007827990
    // BEGIN: module_task_write_ts1755007827991
    my_if task_vif_inst();
    task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
        output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
        if (en) begin
            vif_data = data_val;
            vif_valid = 1'b1;
            vif_ready = 1'b0;
        end else begin
            vif_data = 8'h0;
            vif_valid = 1'b0;
            vif_ready = 1'b1;
        end
    endtask
    always_comb begin
        update_vif_signals(inj_d_1755007827990_693, inj_data_a_1755007827990_6, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        inj_task_output_valid_1755007827990_731 = task_vif_inst.valid;
    end
    // END: module_task_write_ts1755007827991

    always_ff @(posedge clk) begin
        inj_q_1755007827990_150 <= inj_d_1755007827990_693;
    end
    // END: mod_seq_reg_ts1755007827990

    casez_xz casez_xz_inst_1755007827990_4544 (
        .out_res(inj_out_res_1755007827990_548),
        .in_val(inj_in_val_1755007827990_724)
    );
    dup_cond dup_cond_inst_1755007827990_6559 (
        .result1(inj_result1_1755007827990_829),
        .result2(inj_result2_1755007827990_9),
        .control(inj_control_1755007827990_879),
        .data_a(inj_data_a_1755007827990_6),
        .data_b(inj_data_b_1755007827990_970)
    );
endmodule

