interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module PragmaProtectBoundaries (
    input logic start_protect,
    output logic protected_active
);
logic internal_state;
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state = start_protect;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign protected_active = internal_state;
endmodule

module child_module_v1_config_dummy (
    input logic i,
    output logic o
);
    assign o = ~i; 
endmodule

module module_sequence_different_if (
    input logic [31:0] input1,
    input logic [7:0] input2_byte,
    output logic sequence_valid
);
    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = input1;
        sif2_port.status_byte = input2_byte;
        sequence_valid = 1'b1;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_enable_pa_1755007787657_376,
    input wire inj_g_in_1755007787657_403,
    input logic [7:0] inj_in3_dd_1755007787665_300,
    input logic [7:0] inj_in4_dd_1755007787665_544,
    input logic [1:0] inj_in_val_1755007787657_670,
    input logic [7:0] inj_input2_byte_1755007787659_689,
    input logic [31:0] inj_input_pa_1755007787657_867,
    input logic [3:0] inj_input_slice_pa_1755007787657_714,
    input logic [4:0] inj_read_address_1755007787660_384,
    input logic [2:0] inj_shamt_1755007787662_385,
    input logic [4:0] inj_write_address_1755007787660_638,
    input wire reset,
    output logic [7:0] inj_data_out_1755007787659_57,
    output logic [7:0] inj_data_out_1755007787669_741,
    output wire inj_g_out_and_1755007787657_243,
    output wire inj_g_out_or_1755007787657_839,
    output logic [7:0] inj_left_shift_1755007787662_877,
    output logic inj_o_1755007787664_627,
    output logic [7:0] inj_out1_dd_1755007787665_778,
    output logic [7:0] inj_out2_dd_1755007787665_492,
    output logic inj_out_pd_1755007787658_947,
    output logic [7:0] inj_out_reg_t_1755007787663_995,
    output reg inj_out_res_1755007787657_119,
    output logic [7:0] inj_output_pa_1755007787657_103,
    output logic [7:0] inj_output_pa_element1_1755007787657_581,
    output logic inj_protected_active_1755007787667_268,
    output logic [7:0] inj_read_data_1755007787660_302,
    output logic [7:0] inj_right_shift_arith_1755007787662_151,
    output logic [7:0] inj_right_shift_logic_1755007787662_782,
    output logic inj_sequence_valid_1755007787659_565
);
    // BEGIN: Module_GatePrimitives_ts1755007787657
    // BEGIN: case_basic_ts1755007787657
    // BEGIN: module_packed_array_ts1755007787658
    logic [7:0] my_packed_array[0:3] ;
    // BEGIN: SynchronousMemory_ts1755007787661
    logic [7:0] mem_ts1755007787661 [0:31];
        // BEGIN: ModSampledVarLogic_ts1755007787669
        logic [7:0] __Vsampled_state = 8'hAB; 
        logic [7:0] internal_reg_ts1755007787669;
        always @(posedge clk) begin
        if (inj_input_slice_pa_1755007787657_714 == 4'd5) begin 
            internal_reg_ts1755007787669 <= __Vsampled_state + inj_input_slice_pa_1755007787657_714; 
        end else if (inj_input_slice_pa_1755007787657_714 > 4'd8) begin 
            internal_reg_ts1755007787669 <= {4'h0, inj_input_slice_pa_1755007787657_714} - 1; 
        end else begin
            internal_reg_ts1755007787669 <= 8'hFF;
        end
        end
        assign inj_data_out_1755007787669_741 = internal_reg_ts1755007787669;
        // END: ModSampledVarLogic_ts1755007787669

        PragmaProtectBoundaries PragmaProtectBoundaries_inst_1755007787667_3576 (
            .protected_active(inj_protected_active_1755007787667_268),
            .start_protect(inj_enable_pa_1755007787657_376)
        );
        // BEGIN: split_multi_nb_in_if_ts1755007787666
        always @(posedge clk) begin
            if (inj_enable_pa_1755007787657_376) begin
                inj_out1_dd_1755007787665_778 <= inj_input2_byte_1755007787659_689 + mem_ts1755007787661;
                inj_out2_dd_1755007787665_492 <= inj_in3_dd_1755007787665_300 - inj_in4_dd_1755007787665_544;
            end else begin
                inj_out1_dd_1755007787665_778 <= inj_input2_byte_1755007787659_689 * mem_ts1755007787661;
                inj_out2_dd_1755007787665_492 <= inj_in3_dd_1755007787665_300 / (inj_in4_dd_1755007787665_544 + 1);
            end
        end
        // END: split_multi_nb_in_if_ts1755007787666

        child_module_v1_config_dummy child_module_v1_config_dummy_inst_1755007787664_8830 (
            .i(inj_enable_pa_1755007787657_376),
            .o(inj_o_1755007787664_627)
        );
        // BEGIN: split_if_empty_branches_ts1755007787663
        always @(posedge clk) begin
            if (inj_enable_pa_1755007787657_376) begin
            end else begin
            end
        end
        // END: split_if_empty_branches_ts1755007787663

        // BEGIN: shift_ops_ts1755007787662
        assign inj_left_shift_1755007787662_877 = mem_ts1755007787661 << inj_shamt_1755007787662_385;
        assign inj_right_shift_logic_1755007787662_782 = mem_ts1755007787661 >> inj_shamt_1755007787662_385;
        assign inj_right_shift_arith_1755007787662_151 = mem_ts1755007787661 >>> inj_shamt_1755007787662_385;
        // END: shift_ops_ts1755007787662

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755007787660_302 <= 8'h0;
        end else begin
            if (inj_enable_pa_1755007787657_376) begin
                mem_ts1755007787661[inj_write_address_1755007787660_638] <= inj_input2_byte_1755007787659_689;
            end
            inj_read_data_1755007787660_302 <= mem_ts1755007787661[inj_read_address_1755007787660_384];
        end
    end
    // END: SynchronousMemory_ts1755007787661

    // BEGIN: cu_base_ts1755007787660
    assign inj_data_out_1755007787659_57 = inj_input2_byte_1755007787659_689;
    // END: cu_base_ts1755007787660

    module_sequence_different_if module_sequence_different_if_inst_1755007787659_4440 (
        .input1(inj_input_pa_1755007787657_867),
        .input2_byte(inj_input2_byte_1755007787659_689),
        .sequence_valid(inj_sequence_valid_1755007787659_565)
    );
    // BEGIN: ProgramDefinition_ts1755007787658
    assign inj_out_pd_1755007787658_947 = reset;
    // END: ProgramDefinition_ts1755007787658

    always_comb begin
        if (inj_enable_pa_1755007787657_376) begin
            my_packed_array[0] = inj_input_pa_1755007787657_867[7:0];
            my_packed_array[1] = inj_input_pa_1755007787657_867[15:8];
            my_packed_array[2] = inj_input_pa_1755007787657_867[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = inj_input_slice_pa_1755007787657_714;
    end
    assign inj_output_pa_1755007787657_103 = my_packed_array[3];
    assign inj_output_pa_element1_1755007787657_581 = my_packed_array[1];
    // END: module_packed_array_ts1755007787658

    always_comb begin
        inj_out_res_1755007787657_119 = 1'b0;
        case (inj_in_val_1755007787657_670)
            2'b00: inj_out_res_1755007787657_119 = 1'b0;
            2'b01: inj_out_res_1755007787657_119 = 1'b1;
            2'b10: inj_out_res_1755007787657_119 = 1'b0;
            2'b11: inj_out_res_1755007787657_119 = 1'b1;
        endcase
    end
    // END: case_basic_ts1755007787657

    and a1 (inj_g_out_and_1755007787657_243, inj_g_in_1755007787657_403, inj_g_in_1755007787657_403);
    or  o1 (inj_g_out_or_1755007787657_839 , inj_g_in_1755007787657_403, inj_g_in_1755007787657_403);
    // END: Module_GatePrimitives_ts1755007787657
endmodule

