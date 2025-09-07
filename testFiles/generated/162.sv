module child_module_v1_config_dummy (
    input logic i,
    output logic o
);
    assign o = ~i; 
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755007807396_590,
    input logic inj_cond2_1755007807394_574,
    input logic [7:0] inj_in1_1755007807392_345,
    input logic [7:0] inj_in2_1755007807392_980,
    input logic [7:0] inj_in3_1755007807392_346,
    input logic inj_in_its_1755007807391_876,
    input logic [1:0] inj_in_val_1755007807391_18,
    input wire reset,
    output logic inj_dout_1755007807391_491,
    output logic inj_nand_out_1755007807392_760,
    output logic inj_nor_out_1755007807392_125,
    output logic inj_o_1755007807392_392,
    output logic inj_out_a_1755007807396_631,
    output int inj_out_b_1755007807396_746,
    output logic inj_out_data_pull0_1755007807391_512,
    output logic inj_out_data_pull1_1755007807391_816,
    output logic inj_out_its_1755007807391_430,
    output logic [7:0] inj_out_nested_a_1755007807394_972,
    output logic [7:0] inj_out_nested_b_1755007807394_607,
    output reg inj_out_res_1755007807391_62,
    output reg inj_out_res_1755007807393_210,
    output logic inj_out_sub_1755007807393_415,
    output logic inj_xnor_out_1755007807392_859
);
    // BEGIN: ImplicitTimeScaleModule_ts1755007807391
    // BEGIN: case_basic_ts1755007807391
    // BEGIN: ModRegister_ts1755007807391
    // BEGIN: module_with_unconnected_drive_ts1755007807392
    // BEGIN: remaining_reduction_ops_ts1755007807392
    // BEGIN: case_basic_ts1755007807393
    // BEGIN: mod_sub_ts1755007807394
    // BEGIN: mod_split_nested_ts1755007807395
    logic [7:0]  split_nested_var_ts1755007807395;
    logic [7:0] other_nested_var_ts1755007807395;
        // BEGIN: ModuleBasic_ts1755007807397
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007807397;
        int   d_ts1755007807397;
        always_comb begin
            logic temp_v_ts1755007807397;
            temp_v_ts1755007807397 = d_ts1755007807397;
            c_ts1755007807397      = temp_v_ts1755007807397;
        end
        assign inj_out_a_1755007807396_631 = inj_cond2_1755007807394_574;
        assign d_ts1755007807397     = inj_b_1755007807396_590;
        assign inj_out_b_1755007807396_746 = d_ts1755007807397 + P1 + LP1;
        // END: ModuleBasic_ts1755007807397

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var_ts1755007807395 <= 8'b0;
            other_nested_var_ts1755007807395 <= 8'b0;
        end else begin
            split_nested_var_ts1755007807395 <= 8'h11; 
            other_nested_var_ts1755007807395 <= 8'h22; 
            if (inj_in_its_1755007807391_876) begin
                split_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 + 10;
                other_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 + 20;
                if (inj_cond2_1755007807394_574) begin
                    split_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 + 100;
                    other_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 + 200;
                end
            end else begin
                split_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 - 10;
                other_nested_var_ts1755007807395 <= inj_in1_1755007807392_345 - 20;
            end
        end
    end
    always_comb begin
        inj_out_nested_a_1755007807394_972 = split_nested_var_ts1755007807395;
        inj_out_nested_b_1755007807394_607 = other_nested_var_ts1755007807395;
    end
    // END: mod_split_nested_ts1755007807395

    assign inj_out_sub_1755007807393_415 = reset;
    // END: mod_sub_ts1755007807394

    always_comb begin
        inj_out_res_1755007807393_210 = 1'b0;
        case (inj_in_val_1755007807391_18)
            2'b00: inj_out_res_1755007807393_210 = 1'b0;
            2'b01: inj_out_res_1755007807393_210 = 1'b1;
            2'b10: inj_out_res_1755007807393_210 = 1'b0;
            2'b11: inj_out_res_1755007807393_210 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007807393

    child_module_v1_config_dummy child_module_v1_config_dummy_inst_1755007807392_9222 (
        .o(inj_o_1755007807392_392),
        .i(inj_in_its_1755007807391_876)
    );
    assign inj_nand_out_1755007807392_760 = ~&inj_in1_1755007807392_345;
    assign inj_nor_out_1755007807392_125 = ~|inj_in2_1755007807392_980;
    assign inj_xnor_out_1755007807392_859 = ^~inj_in3_1755007807392_346;
    // END: remaining_reduction_ops_ts1755007807392

    assign inj_out_data_pull1_1755007807391_816 = inj_in_its_1755007807391_876;
    assign inj_out_data_pull0_1755007807391_512 = ~inj_in_its_1755007807391_876;
    // END: module_with_unconnected_drive_ts1755007807392

    always @* begin
        inj_dout_1755007807391_491 = inj_in_its_1755007807391_876;
    end
    // END: ModRegister_ts1755007807391

    always_comb begin
        inj_out_res_1755007807391_62 = 1'b0;
        case (inj_in_val_1755007807391_18)
            2'b00: inj_out_res_1755007807391_62 = 1'b0;
            2'b01: inj_out_res_1755007807391_62 = 1'b1;
            2'b10: inj_out_res_1755007807391_62 = 1'b0;
            2'b11: inj_out_res_1755007807391_62 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007807391

    assign inj_out_its_1755007807391_430 = inj_in_its_1755007807391_876;
    // END: ImplicitTimeScaleModule_ts1755007807391
endmodule

