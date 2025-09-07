module snippet (
    input wire clk,
    input logic [7:0] inj_data0_1755007917172_698,
    input logic [7:0] inj_data1_1755007917172_623,
    input logic [7:0] inj_data2_1755007917172_440,
    input logic [7:0] inj_data3_1755007917172_216,
    input logic inj_din_a_1755007917172_412,
    input logic inj_din_b_1755007917172_60,
    input logic [1:0] inj_sel_code_1755007917172_321,
    input wire reset,
    output logic inj_dout_a_1755007917172_539,
    output logic inj_dout_b_1755007917172_519,
    output logic [7:0] inj_selected_data_1755007917172_591
);
    // BEGIN: ModMultipleAlways_ts1755007917172
    // BEGIN: IfElseIfChain_ts1755007917172
    always_comb begin
        if (inj_sel_code_1755007917172_321 == 2'b00) begin
            inj_selected_data_1755007917172_591 = inj_data0_1755007917172_698;
        end else if (inj_sel_code_1755007917172_321 == 2'b01) begin
            inj_selected_data_1755007917172_591 = inj_data1_1755007917172_623;
        end else if (inj_sel_code_1755007917172_321 == 2'b10) begin
            inj_selected_data_1755007917172_591 = inj_data2_1755007917172_440;
        end else begin
            inj_selected_data_1755007917172_591 = inj_data3_1755007917172_216;
        end
    end
    // END: IfElseIfChain_ts1755007917172

    always @(posedge clk or negedge reset) begin 
    if (!reset) begin 
        inj_dout_a_1755007917172_539 <= 1'b0;
    end else begin
        inj_dout_a_1755007917172_539 <= inj_din_a_1755007917172_412; 
    end
    end
    always @(posedge clk) begin 
    inj_dout_b_1755007917172_519 <= inj_din_b_1755007917172_60; 
    end
    // END: ModMultipleAlways_ts1755007917172
endmodule

