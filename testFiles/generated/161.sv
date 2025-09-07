module Comb_Case (
    input wire [3:0] in0,
    input wire [3:0] in1,
    input wire [3:0] in2,
    input wire [3:0] in3,
    input wire [1:0] sel,
    output reg [3:0] mux_out
);
    always_comb begin
        case (sel)
            2'b00: mux_out = in0;
            2'b01: mux_out = in1;
            2'b10: mux_out = in2;
            default: mux_out = in3;
        endcase
    end
endmodule

module LintCombBlockAssign (
    input logic in_c,
    input logic in_d,
    output logic out_e
);
    always_comb begin
        out_e = in_c & in_d;
    end
endmodule

module SynchronousMemory (
    input logic clk,
    input logic [4:0] read_address,
    input logic rst,
    input logic [4:0] write_address,
    input logic [7:0] write_data,
    input logic write_en,
    output logic [7:0] read_data
);
    logic [7:0] mem [0:31];
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            read_data <= 8'h0;
        end else begin
            if (write_en) begin
                mem[write_address] <= write_data;
            end
            read_data <= mem[read_address];
        end
    end
endmodule

module cu_timeunit_mod (
    input logic clk,
    output logic reset
);
    logic internal_sig;
    always_ff @(posedge clk) begin
        reset <= 1'b0;
        internal_sig = clk;
    end
endmodule

module module_bitfield_concat (
    input logic [7:0] input_bf,
    input logic [3:0] input_bf_slice,
    output logic [7:0] output_bf,
    output logic [3:0] output_bf_slice
);
    logic [7:0] my_bitfield ;
    always_comb begin
        if (input_bf[7]) begin
            my_bitfield = input_bf;
        end else begin
            my_bitfield = {input_bf[0], input_bf[7:1]};
        end
        my_bitfield[3:0] = input_bf_slice;
    end
    assign output_bf = my_bitfield;
    assign output_bf_slice = my_bitfield[3:0];
endmodule

module packed_struct_module (
    input wire [15:0] in_packed_data,
    output wire [7:0] out_byte
);
    typedef struct packed {
        logic [7:0] byte1;
        logic [7:0] byte2;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = in_packed_data;
    assign out_byte = data_struct.byte1;
endmodule

module snippet (
    input wire clk,
    input bit inj_enable_crypto_1755007807074_571,
    input wire [3:0] inj_in0_1755007807076_862,
    input wire [3:0] inj_in1_1755007807076_13,
    input wire [3:0] inj_in2_1755007807076_615,
    input wire [3:0] inj_in3_1755007807076_370,
    input logic inj_in_d_1755007807077_796,
    input wire [15:0] inj_in_packed_data_1755007807081_475,
    input logic [7:0] inj_input_bf_1755007807073_689,
    input logic [3:0] inj_input_bf_slice_1755007807073_702,
    input logic [4:0] inj_read_address_1755007807073_803,
    input wire [1:0] inj_sel_1755007807076_759,
    input logic [31:0] inj_wide_data_in_1755007807074_543,
    input logic [4:0] inj_write_address_1755007807073_906,
    input logic inj_write_en_1755007807073_21,
    input wire reset,
    output bit inj_crypto_active_1755007807074_146,
    output reg [3:0] inj_mux_out_1755007807076_615,
    output wire [7:0] inj_out_byte_1755007807081_158,
    output logic inj_out_cmp_1755007807078_907,
    output logic inj_out_e_1755007807077_387,
    output logic [7:0] inj_out_ops_1755007807078_196,
    output logic [7:0] inj_output_bf_1755007807073_135,
    output logic [3:0] inj_output_bf_slice_1755007807073_587,
    output logic [7:0] inj_read_data_1755007807073_776,
    output logic [7:0] inj_read_data_1755007807076_238,
    output logic inj_reset_1755007807075_213,
    output logic [31:0] inj_wide_data_out_1755007807074_920
);
    // BEGIN: SynchronousMemory_ts1755007807074
    logic [7:0] mem_ts1755007807073 [0:31];
        // BEGIN: Module_BasicSyntax_ts1755007807079
        logic [7:0] temp_ts1755007807079;
            packed_struct_module packed_struct_module_inst_1755007807081_9556 (
                .in_packed_data(inj_in_packed_data_1755007807081_475),
                .out_byte(inj_out_byte_1755007807081_158)
            );
        always_comb begin
            temp_ts1755007807079 = mem_ts1755007807073 + inj_input_bf_1755007807073_689;
        end
        assign inj_out_ops_1755007807078_196 = (mem_ts1755007807073 & inj_input_bf_1755007807073_689) | (mem_ts1755007807073 ^ inj_input_bf_1755007807073_689);
        assign inj_out_cmp_1755007807078_907 = (mem_ts1755007807073 == inj_input_bf_1755007807073_689);
        // END: Module_BasicSyntax_ts1755007807079

        LintCombBlockAssign LintCombBlockAssign_inst_1755007807077_7039 (
            .out_e(inj_out_e_1755007807077_387),
            .in_c(inj_write_en_1755007807073_21),
            .in_d(inj_in_d_1755007807077_796)
        );
        Comb_Case Comb_Case_inst_1755007807076_8670 (
            .in1(inj_in1_1755007807076_13),
            .in2(inj_in2_1755007807076_615),
            .in3(inj_in3_1755007807076_370),
            .sel(inj_sel_1755007807076_759),
            .mux_out(inj_mux_out_1755007807076_615),
            .in0(inj_in0_1755007807076_862)
        );
        SynchronousMemory SynchronousMemory_inst_1755007807076_7525 (
            .write_en(inj_write_en_1755007807073_21),
            .read_data(inj_read_data_1755007807076_238),
            .clk(clk),
            .read_address(inj_write_address_1755007807073_906),
            .rst(reset),
            .write_address(inj_read_address_1755007807073_803),
            .write_data(mem_ts1755007807073)
        );
        cu_timeunit_mod cu_timeunit_mod_inst_1755007807075_5500 (
            .clk(clk),
            .reset(inj_reset_1755007807075_213)
        );
        // BEGIN: PragmaProtectKeyBlock_ts1755007807074
    `ifdef SLANG_PRAGMA
    `protect key
    `endif
    `ifdef SLANG_PRAGMA
    `protect block
    `endif
    assign inj_crypto_active_1755007807074_146 = inj_enable_crypto_1755007807074_571;
        // END: PragmaProtectKeyBlock_ts1755007807074

        // BEGIN: module_using_package_param_ts1755007807074
        assign inj_wide_data_out_1755007807074_920 = inj_wide_data_in_1755007807074_543;
        // END: module_using_package_param_ts1755007807074

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755007807073_776 <= 8'h0;
        end else begin
            if (inj_write_en_1755007807073_21) begin
                mem_ts1755007807073[inj_write_address_1755007807073_906] <= inj_input_bf_1755007807073_689;
            end
            inj_read_data_1755007807073_776 <= mem_ts1755007807073[inj_read_address_1755007807073_803];
        end
    end
    // END: SynchronousMemory_ts1755007807074

    module_bitfield_concat module_bitfield_concat_inst_1755007807073_6347 (
        .input_bf(inj_input_bf_1755007807073_689),
        .input_bf_slice(inj_input_bf_slice_1755007807073_702),
        .output_bf(inj_output_bf_1755007807073_135),
        .output_bf_slice(inj_output_bf_slice_1755007807073_587)
    );
endmodule

