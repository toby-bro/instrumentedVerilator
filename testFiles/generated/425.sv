module snippet (
    input wire clk,
    input logic inj_d_in_1755007896441_719,
    input logic [7:0] inj_data_in_1755007896441_116,
    input logic [3:0] inj_data_in_1755007896444_837,
    input wire reset,
    output logic [7:0] inj_data_out_1755007896444_413,
    output logic [7:0] inj_out_nested_a_1755007896441_48,
    output logic [7:0] inj_out_nested_b_1755007896441_566,
    output logic [7:0] inj_out_v_1755007896443_792,
    output logic inj_q_out_1755007896441_451
);
    // BEGIN: LogicDependencyChain_ts1755007896441
    logic q1_ts1755007896441, q2_ts1755007896441;
        // BEGIN: mod_split_nested_ts1755007896443
        logic [7:0]  split_nested_var_ts1755007896442;
        logic [7:0] other_nested_var_ts1755007896442;
            // BEGIN: ModSampledVarLogic_ts1755007896445
            logic [7:0] __Vsampled_state = 8'hAB; 
            logic [7:0] internal_reg_ts1755007896444;
            always @(posedge clk) begin
            if (inj_data_in_1755007896444_837 == 4'd5) begin 
                internal_reg_ts1755007896444 <= __Vsampled_state + inj_data_in_1755007896444_837; 
            end else if (inj_data_in_1755007896444_837 > 4'd8) begin 
                internal_reg_ts1755007896444 <= {4'h0, inj_data_in_1755007896444_837} - 1; 
            end else begin
                internal_reg_ts1755007896444 <= 8'hFF;
            end
            end
            assign inj_data_out_1755007896444_413 = internal_reg_ts1755007896444;
            // END: ModSampledVarLogic_ts1755007896445

            // BEGIN: ModVectorAdd_ts1755007896443
            assign inj_out_v_1755007896443_792 = inj_data_in_1755007896441_116 + 8'h01;
            // END: ModVectorAdd_ts1755007896443

        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                split_nested_var_ts1755007896442 <= 8'b0;
                other_nested_var_ts1755007896442 <= 8'b0;
            end else begin
                split_nested_var_ts1755007896442 <= 8'h11; 
                other_nested_var_ts1755007896442 <= 8'h22; 
                if (q2_ts1755007896441) begin
                    split_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 + 10;
                    other_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 + 20;
                    if (q1_ts1755007896441) begin
                        split_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 + 100;
                        other_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 + 200;
                    end
                end else begin
                    split_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 - 10;
                    other_nested_var_ts1755007896442 <= inj_data_in_1755007896441_116 - 20;
                end
            end
        end
        always_comb begin
            inj_out_nested_a_1755007896441_48 = split_nested_var_ts1755007896442;
            inj_out_nested_b_1755007896441_566 = other_nested_var_ts1755007896442;
        end
        // END: mod_split_nested_ts1755007896443

    always @(posedge clk) begin
        q1_ts1755007896441 <= inj_d_in_1755007896441_719;
    end
    always @(q1_ts1755007896441) begin
        q2_ts1755007896441 = ~q1_ts1755007896441;
    end
    assign inj_q_out_1755007896441_451 = q2_ts1755007896441;
    // END: LogicDependencyChain_ts1755007896441
endmodule

