module ModSampledVarLogic (
    input logic clk,
    input logic [3:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] __Vsampled_state = 8'hAB; 
    logic [7:0] internal_reg;
    always @(posedge clk) begin
    if (data_in == 4'd5) begin 
        internal_reg <= __Vsampled_state + data_in; 
    end else if (data_in > 4'd8) begin 
        internal_reg <= {4'h0, data_in} - 1; 
    end else begin
        internal_reg <= 8'hFF;
    end
    end
    assign data_out = internal_reg;
endmodule

module mod_automatic_task (
    input int i_val,
    output int o_val
);
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val;
        update_val(i_val, temp_val);
        o_val = temp_val;
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_data_in_1755007914992_125,
    input int inj_i_val_1755007914992_669,
    input logic [15:0] inj_in1_1755007914991_423,
    input logic [15:0] inj_in2_1755007914991_146,
    input logic inj_sel_1755007914991_932,
    input wire reset,
    output wire inj_data_d_1755007914992_123,
    output logic [7:0] inj_data_out_1755007914992_240,
    output int inj_o_val_1755007914992_731,
    output logic [15:0] inj_out1_1755007914991_599,
    output logic [15:0] inj_out2_1755007914991_325
);
    // BEGIN: procedural_complex_ts1755007914991
    logic [15:0] temp1_ts1755007914991;
    logic [15:0] temp2_ts1755007914991;
        mod_automatic_task mod_automatic_task_inst_1755007914992_6574 (
            .i_val(inj_i_val_1755007914992_669),
            .o_val(inj_o_val_1755007914992_731)
        );
        // BEGIN: simple_logic_b_ts1755007914992
        assign inj_data_d_1755007914992_123 = clk;
        // END: simple_logic_b_ts1755007914992

        ModSampledVarLogic ModSampledVarLogic_inst_1755007914992_5451 (
            .data_out(inj_data_out_1755007914992_240),
            .clk(clk),
            .data_in(inj_data_in_1755007914992_125)
        );
    always_comb begin
        temp1_ts1755007914991 = (inj_in1_1755007914991_423 + inj_in2_1755007914991_146) * 10;
        if (inj_sel_1755007914991_932) begin
            temp2_ts1755007914991 = temp1_ts1755007914991 ^ (inj_in1_1755007914991_423 >>> 2);
            inj_out1_1755007914991_599 = temp2_ts1755007914991 & inj_in2_1755007914991_146;
        end else begin
            temp2_ts1755007914991 = temp1_ts1755007914991 | (inj_in2_1755007914991_146 <<< 3);
            inj_out1_1755007914991_599 = temp2_ts1755007914991 + inj_in1_1755007914991_423;
        end
        inj_out2_1755007914991_325 = temp1_ts1755007914991 - temp2_ts1755007914991;
    end
    // END: procedural_complex_ts1755007914991
endmodule

