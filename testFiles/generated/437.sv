module ModuleImplicitPort (
    input logic signed [7:0] data,
    output logic out_valid
);
    logic valid;
    assign valid = |data;
    assign out_valid = valid;
endmodule

module nested_macro_expansion (
    input int in_val,
    output int out_val
);
    `define LVL1(x) ((x) + 1)
    `define LVL2(y) `LVL1((y) * 2)
    `define LVL3(z) `LVL2((z) / 3)
    int nested_result;
    always_comb begin
        nested_result = `LVL3(`LVL1(in_val));
    end
    assign out_val = nested_result;
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755007900238_670,
    input logic [1:0] inj_case_expr_1755007900236_661,
    input logic signed [7:0] inj_data_1755007900236_668,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007900243_129,
    input wire [15:0] inj_dffcl_data_in1_1755007900243_328,
    input wire [15:0] inj_dffcl_data_in2_1755007900243_671,
    input logic inj_din_a_1755007900235_683,
    input logic inj_din_b_1755007900235_532,
    input logic [3:0] inj_i_bind_control_1755007900236_720,
    input logic [7:0] inj_in2_z_1755007900237_893,
    input logic [3:0] inj_in_a_1755007900242_829,
    input wire reset,
    output logic [7:0] inj_data_out_1755007900237_826,
    output logic [15:0] inj_dffcl_data_out_1755007900243_368,
    output logic inj_dout_a_1755007900235_977,
    output logic inj_dout_b_1755007900235_437,
    output logic [4:0] inj_internal_out_1755007900236_750,
    output logic inj_o_bind_status_1755007900236_917,
    output logic [7:0] inj_out1_z_1755007900237_943,
    output logic [7:0] inj_out2_z_1755007900237_740,
    output logic inj_out_a_1755007900238_565,
    output int inj_out_b_1755007900238_768,
    output int inj_out_val_1755007900240_524,
    output logic inj_out_valid_1755007900236_343,
    output logic [7:0] inj_out_vec_y_1755007900239_520,
    output logic [3:0] inj_out_y_1755007900242_765,
    output logic inj_task_out_1755007900248_468
);
    // BEGIN: ModMultipleAlways_ts1755007900235
    // BEGIN: case_priority_overlapping_mod_ts1755007900236
    // BEGIN: module_to_bind_ts1755007900236
    // BEGIN: cu_base_ts1755007900237
    // BEGIN: split_diff_vars_branches_ts1755007900238
    // BEGIN: ModuleBasic_ts1755007900238
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755007900238;
    int   d_ts1755007900238;
    always_comb begin
        logic temp_v_ts1755007900238;
            // BEGIN: task_example_ts1755007900248
            task automatic process_data (input logic data);
                logic temp_ts1755007900248;
                temp_ts1755007900248 = data; 
            endtask 
            assign inj_task_out_1755007900248_468 = temp_v_ts1755007900238;
            // END: task_example_ts1755007900248

            // BEGIN: deep_ff_control_logic_ts1755007900245
            always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_dffcl_data_out_1755007900243_368 <= 16'h0000;
            end else begin
                case (inj_dffcl_ctrl_mode_1755007900243_129)
                    4'd0: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 + inj_dffcl_data_in2_1755007900243_671;
                    4'd1: begin
                        if (inj_dffcl_data_in1_1755007900243_328 > inj_dffcl_data_in2_1755007900243_671) begin
                            case (inj_dffcl_ctrl_mode_1755007900243_129[1:0])
                                2'b00: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 - inj_dffcl_data_in2_1755007900243_671;
                                2'b01: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 & inj_dffcl_data_in2_1755007900243_671;
                                default: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 | inj_dffcl_data_in2_1755007900243_671;
                            endcase
                        end else begin
                            case (inj_dffcl_ctrl_mode_1755007900243_129[1:0])
                                2'b00: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in2_1755007900243_671 - inj_dffcl_data_in1_1755007900243_328;
                                2'b01: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 ^ inj_dffcl_data_in2_1755007900243_671;
                                default: inj_dffcl_data_out_1755007900243_368 <= ~inj_dffcl_data_in1_1755007900243_328;
                            endcase
                        end
                    end
                    4'd2: begin
                        casez (inj_dffcl_data_in1_1755007900243_328[15:13])
                            3'b000: inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in2_1755007900243_671;
                            3'b001: inj_dffcl_data_out_1755007900243_368 <= ~inj_dffcl_data_in2_1755007900243_671;
                            3'b01?: begin
                                if (inj_dffcl_data_in2_1755007900243_671[0]) inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 << 1;
                                else inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 >> 1;
                            end
                            3'b1??: begin
                                if (inj_dffcl_ctrl_mode_1755007900243_129[0]) inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 + 1;
                                else inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328 - 1;
                            end
                            default: inj_dffcl_data_out_1755007900243_368 <= 16'hAAAA;
                        endcase
                    end
                    default: begin
                        if (inj_dffcl_ctrl_mode_1755007900243_129[2]) inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in1_1755007900243_328;
                        else inj_dffcl_data_out_1755007900243_368 <= inj_dffcl_data_in2_1755007900243_671;
                    end
                endcase
            end
            end
            // END: deep_ff_control_logic_ts1755007900245

            // BEGIN: BitwiseAssign_ts1755007900242
            assign inj_out_y_1755007900242_765 = inj_in_a_1755007900242_829 ^ inj_i_bind_control_1755007900236_720;
            // END: BitwiseAssign_ts1755007900242

            nested_macro_expansion nested_macro_expansion_inst_1755007900240_8448 (
                .in_val(d_ts1755007900238),
                .out_val(inj_out_val_1755007900240_524)
            );
            // BEGIN: split_vector_assign_ts1755007900239
            always @(posedge clk) begin
                if (inj_din_a_1755007900235_683) begin
                    inj_out_vec_y_1755007900239_520[3:0] <= inj_data_1755007900236_668[3:0];
                    inj_out_vec_y_1755007900239_520[7:4] <= inj_data_1755007900236_668[7:4] + 1;
                end else begin
                    inj_out_vec_y_1755007900239_520 <= 8'hFF;
                end
            end
            // END: split_vector_assign_ts1755007900239

        temp_v_ts1755007900238 = d_ts1755007900238;
        c_ts1755007900238      = temp_v_ts1755007900238;
    end
    assign inj_out_a_1755007900238_565 = inj_din_a_1755007900235_683;
    assign d_ts1755007900238     = inj_b_1755007900238_670;
    assign inj_out_b_1755007900238_768 = d_ts1755007900238 + P1 + LP1;
    // END: ModuleBasic_ts1755007900238

    always @(posedge clk) begin
        if (inj_din_a_1755007900235_683) begin
            inj_out1_z_1755007900237_943 <= inj_data_1755007900236_668;
        end else begin
            inj_out2_z_1755007900237_740 <= inj_in2_z_1755007900237_893;
        end
    end
    // END: split_diff_vars_branches_ts1755007900238

    assign inj_data_out_1755007900237_826 = inj_data_1755007900236_668;
    // END: cu_base_ts1755007900237

    always_comb inj_o_bind_status_1755007900236_917 = |inj_i_bind_control_1755007900236_720;
    // END: module_to_bind_ts1755007900236

    always @* begin
        priority casez (inj_case_expr_1755007900236_661)
            2'b1?: inj_internal_out_1755007900236_750 = 5;
            2'b?1: inj_internal_out_1755007900236_750 = 6;  
            2'b0?: inj_internal_out_1755007900236_750 = 7;
            2'b?0: inj_internal_out_1755007900236_750 = 8;  
            default: inj_internal_out_1755007900236_750 = 9;
        endcase
    end
    // END: case_priority_overlapping_mod_ts1755007900236

    ModuleImplicitPort ModuleImplicitPort_inst_1755007900236_4084 (
        .data(inj_data_1755007900236_668),
        .out_valid(inj_out_valid_1755007900236_343)
    );
    always @(posedge clk or negedge reset) begin 
    if (!reset) begin 
        inj_dout_a_1755007900235_977 <= 1'b0;
    end else begin
        inj_dout_a_1755007900235_977 <= inj_din_a_1755007900235_683; 
    end
    end
    always @(posedge clk) begin 
    inj_dout_b_1755007900235_437 <= inj_din_b_1755007900235_532; 
    end
    // END: ModMultipleAlways_ts1755007900235
endmodule

