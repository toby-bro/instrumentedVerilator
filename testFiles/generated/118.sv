module snippet (
    input wire clk,
    input logic inj_a_1755007792308_31,
    input int inj_b_1755007792308_616,
    input logic inj_din_1755007792307_140,
    input logic [7:0] inj_in1_1755007792307_746,
    input logic [7:0] inj_in2_1755007792307_866,
    input logic [2:0] inj_shamt_1755007792308_204,
    input wire reset,
    output logic inj_data_out_1755007792308_488,
    output logic inj_dout_1755007792307_534,
    output logic [7:0] inj_left_shift_1755007792308_711,
    output logic inj_out_1755007792307_437,
    output logic inj_out_a_1755007792308_6,
    output int inj_out_b_1755007792308_225,
    output logic [7:0] inj_right_shift_arith_1755007792308_681,
    output logic [7:0] inj_right_shift_logic_1755007792308_828,
    output logic inj_sum_1755007792308_808
);
    // BEGIN: ModRegister_ts1755007792307
    // BEGIN: reduction_ops_ts1755007792308
    // BEGIN: simple_adder_ts1755007792308
    // BEGIN: shift_ops_ts1755007792308
    // BEGIN: ModuleBasic_ts1755007792308
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007792308;
    int   d_ts1755007792308;
    always_comb begin
        logic temp_v_ts1755007792308;
            // BEGIN: sequential_register_ts1755007792308
            always_ff @(posedge clk or negedge reset) begin
                if (!reset) begin
                    inj_data_out_1755007792308_488 <= 1'b0; 
                end else if (temp_v_ts1755007792308) begin
                    inj_data_out_1755007792308_488 <= inj_a_1755007792308_31; 
                end
            end
            // END: sequential_register_ts1755007792308

        temp_v_ts1755007792308 = d_ts1755007792308;
        c_ts1755007792308      = temp_v_ts1755007792308;
    end
    assign inj_out_a_1755007792308_6 = inj_din_1755007792307_140;
    assign d_ts1755007792308     = inj_b_1755007792308_616;
    assign inj_out_b_1755007792308_225 = d_ts1755007792308 + P1 + LP1;
    // END: ModuleBasic_ts1755007792308

    assign inj_left_shift_1755007792308_711 = inj_in1_1755007792307_746 << inj_shamt_1755007792308_204;
    assign inj_right_shift_logic_1755007792308_828 = inj_in1_1755007792307_746 >> inj_shamt_1755007792308_204;
    assign inj_right_shift_arith_1755007792308_681 = inj_in1_1755007792307_746 >>> inj_shamt_1755007792308_204;
    // END: shift_ops_ts1755007792308

    assign inj_sum_1755007792308_808 = inj_a_1755007792308_31 + inj_din_1755007792307_140;
    // END: simple_adder_ts1755007792308

    assign inj_out_1755007792307_437 = &inj_in1_1755007792307_746 | ^inj_in2_1755007792307_866;
    // END: reduction_ops_ts1755007792308

    always @* begin
        inj_dout_1755007792307_534 = inj_din_1755007792307_140;
    end
    // END: ModRegister_ts1755007792307
endmodule

