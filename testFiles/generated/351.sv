interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module GenerateFor (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : g_loop
            assign data_out[i] = data_in[i];
        end
    endgenerate
endmodule

module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule

module Module_IfNoneParam (
    input int in_port,
    output int out_port
);
    assign out_port = in_port;
endmodule

module SimpleAssign (
    input logic [9:0] val_in,
    output logic [9:0] val_out
);
    assign val_out = val_in;
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module super_outside_class_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_din_b_1755007872350_849,
    input wire [1:0] inj_i_sel_1755007872343_22,
    input wire [3:0] inj_i_val_1755007872343_82,
    input int inj_in_port_1755007872343_598,
    input logic [7:0] inj_in_value_1755007872348_382,
    input logic inj_nm_in_1755007872345_734,
    input logic [15:0] inj_packed_in_1755007872344_384,
    input logic [2:0] inj_shift_val_1755007872354_935,
    input logic [9:0] inj_val_in_1755007872356_370,
    input wire [15:0] inj_value1_1755007872357_791,
    input wire [15:0] inj_value2_1755007872357_469,
    input wire reset,
    output logic [3:0] inj_data_out_1755007872345_410,
    output logic [3:0] inj_data_out_1755007872346_161,
    output reg inj_data_out_1755007872360_362,
    output logic inj_dout_a_1755007872350_376,
    output logic inj_dout_b_1755007872350_35,
    output logic [7:0] inj_field2_o_1755007872344_885,
    output logic [7:0] inj_left_shift_log_1755007872354_419,
    output logic inj_nm_out_1755007872345_722,
    output logic [3:0] inj_o_out_1755007872343_974,
    output logic inj_o_sum_1755007872352_949,
    output logic inj_out_data_q_1755007872348_540,
    output int inj_out_port_1755007872343_30,
    output logic [7:0] inj_out_reg_a_1755007872348_245,
    output logic [7:0] inj_out_reg_b_1755007872348_869,
    output int inj_out_val_1755007872347_949,
    output reg [15:0] inj_result_val_1755007872358_2,
    output logic [7:0] inj_right_shift_arith_1755007872354_127,
    output logic [7:0] inj_right_shift_log_1755007872354_587,
    output logic [9:0] inj_val_out_1755007872356_369,
    output logic [7:0] inj_wide_reg_1755007872352_432
);
    // BEGIN: mod_case_block_attrs_ts1755007872344
    logic [3:0] l_temp_ts1755007872344;
        // BEGIN: mod_split_ff_ts1755007872349
        logic [7:0]  split_reg_var_ts1755007872349;
        logic [7:0] other_reg_var_ts1755007872349;
            // BEGIN: mod_lint_target_ts1755007872352
            logic l_reg_ts1755007872352;
                // BEGIN: mod_event_posedge_ts1755007872360
                always @(posedge clk) begin
                    inj_data_out_1755007872360_362 <= clk;
                end
                // END: mod_event_posedge_ts1755007872360

                // BEGIN: Comb_IfElse_ts1755007872358
                always_comb begin
                    if (reset) begin
                        inj_result_val_1755007872358_2 = inj_value1_1755007872357_791;
                    end else begin
                        inj_result_val_1755007872358_2 = inj_value2_1755007872357_469;
                    end
                end
                // END: Comb_IfElse_ts1755007872358

                SimpleAssign SimpleAssign_inst_1755007872356_1626 (
                    .val_in(inj_val_in_1755007872356_370),
                    .val_out(inj_val_out_1755007872356_369)
                );
                // BEGIN: ShiftOperations_ts1755007872354
                assign inj_left_shift_log_1755007872354_419 = split_reg_var_ts1755007872349 << inj_shift_val_1755007872354_935;
                assign inj_right_shift_log_1755007872354_587 = split_reg_var_ts1755007872349 >> inj_shift_val_1755007872354_935;
                assign inj_right_shift_arith_1755007872354_127 = $signed(split_reg_var_ts1755007872349) >>> inj_shift_val_1755007872354_935;
                // END: ShiftOperations_ts1755007872354

            always_comb begin
                l_reg_ts1755007872352 = 1;
                inj_wide_reg_1755007872352_432 = {clk, reset};
            end
            assign inj_o_sum_1755007872352_949 = clk + reset;
            // END: mod_lint_target_ts1755007872352

            ModMultipleAlways ModMultipleAlways_inst_1755007872350_1692 (
                .dout_a(inj_dout_a_1755007872350_376),
                .dout_b(inj_dout_b_1755007872350_35),
                .clk_a(clk),
                .clk_b(clk),
                .din_a(inj_nm_in_1755007872345_734),
                .din_b(inj_din_b_1755007872350_849),
                .rst_n(reset)
            );
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                split_reg_var_ts1755007872349 <= 8'b0;
                other_reg_var_ts1755007872349 <= 8'b0;
                inj_out_reg_a_1755007872348_245 <= 8'b0;
                inj_out_reg_b_1755007872348_869 <= 8'b0;
            end else begin
                split_reg_var_ts1755007872349 <= inj_in_value_1755007872348_382;
                other_reg_var_ts1755007872349 <= inj_in_value_1755007872348_382 + 2;
                inj_out_reg_a_1755007872348_245 <= split_reg_var_ts1755007872349;
                inj_out_reg_b_1755007872348_869 <= other_reg_var_ts1755007872349;
            end
        end
        // END: mod_split_ff_ts1755007872349

        module_assign_nonblocking module_assign_nonblocking_inst_1755007872348_666 (
            .out_data_q(inj_out_data_q_1755007872348_540),
            .clk(clk),
            .in_value(inj_in_value_1755007872348_382),
            .reset(reset)
        );
        super_outside_class_diag_mod super_outside_class_diag_mod_inst_1755007872347_9010 (
            .out_val(inj_out_val_1755007872347_949),
            .in_val(inj_in_port_1755007872343_598)
        );
        // BEGIN: GenerateFor_ts1755007872346
        genvar i;
        generate
            for (i = 0; i < 4; i = i + 1) begin : g_loop
                assign inj_data_out_1755007872346_161[i] = l_temp_ts1755007872344[i];
            end
        endgenerate
        // END: GenerateFor_ts1755007872346

        GenerateFor GenerateFor_inst_1755007872345_2045 (
            .data_in(l_temp_ts1755007872344),
            .data_out(inj_data_out_1755007872345_410)
        );
        // BEGIN: nested_module_ts1755007872345
        assign inj_nm_out_1755007872345_722 = inj_nm_in_1755007872345_734;
        // END: nested_module_ts1755007872345

        // BEGIN: typedef_struct_public_mod_ts1755007872344
        typedef struct packed {
            logic [7:0] field1_ts1755007872344;
            logic [7:0] field2_ts1755007872344;
        } my_public_packed_struct_t;
        my_public_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755007872344_384;
        end
        assign inj_field2_o_1755007872344_885 = my_struct_var.field2_ts1755007872344;
        // END: typedef_struct_public_mod_ts1755007872344

    always_comb begin
        (* full_case *)
        (* parallel_case *)
        case (inj_i_sel_1755007872343_22)
            2'b00: l_temp_ts1755007872344 = inj_i_val_1755007872343_82;
            2'b01: l_temp_ts1755007872344 = inj_i_val_1755007872343_82 << 1;
            2'b10: l_temp_ts1755007872344 = inj_i_val_1755007872343_82 >> 1;
            default: l_temp_ts1755007872344 = 4'bxxxx;
        endcase
        (* coverage_off *)
        begin : my_named_block
            inj_o_out_1755007872343_974 = l_temp_ts1755007872344;
        end
    end
    // END: mod_case_block_attrs_ts1755007872344

    Module_IfNoneParam Module_IfNoneParam_inst_1755007872343_8436 (
        .out_port(inj_out_port_1755007872343_30),
        .in_port(inj_in_port_1755007872343_598)
    );
endmodule

