module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule

module LintParamUnused #(
    parameter integer UNUSED_PARAM = 8
) (
    input logic in_m,
    output logic out_n
);
    assign out_n = in_m;
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

module ModuleDefinition (
    input wire in_md,
    output logic out_md
);
    assign out_md = in_md;
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

module snippet (
    input wire clk,
    input logic inj_din_b_1755007799502_877,
    input logic [7:0] inj_in1_1755007799501_35,
    input logic [7:0] inj_in2_1755007799501_589,
    input logic [7:0] inj_in3_1755007799501_576,
    input logic inj_in_m_1755007799500_829,
    input bit [3:0] inj_in_mask_z_1755007799502_922,
    input int inj_in_val_1755007799500_546,
    input logic [15:0] inj_packed_in_1755007799500_506,
    input logic [4:0] inj_read_address_1755007799505_280,
    input logic [9:0] inj_val_in_1755007799504_971,
    input wire [15:0] inj_value1_1755007799501_997,
    input wire [15:0] inj_value2_1755007799501_576,
    input logic [4:0] inj_write_address_1755007799505_176,
    input wire reset,
    output logic inj_dout_a_1755007799502_253,
    output logic inj_dout_b_1755007799502_316,
    output logic [7:0] inj_field2_o_1755007799500_779,
    output logic inj_nand_out_1755007799501_704,
    output logic inj_nor_out_1755007799501_709,
    output logic inj_out_i_1755007799500_718,
    output bit [1:0] inj_out_match_type_z_1755007799502_372,
    output logic inj_out_md_1755007799503_705,
    output logic inj_out_n_1755007799500_493,
    output int inj_out_val_1755007799500_705,
    output logic [7:0] inj_read_data_1755007799505_257,
    output reg [15:0] inj_result_val_1755007799501_854,
    output logic [9:0] inj_val_out_1755007799504_33,
    output logic inj_xnor_out_1755007799501_862
);
    // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007799500
    // BEGIN: typedef_struct_mod_ts1755007799500
    typedef struct packed {
        logic [7:0] field1_ts1755007799500;
        logic [7:0] field2_ts1755007799500;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    SynchronousMemory SynchronousMemory_inst_1755007799505_6133 (
        .write_en(inj_in_m_1755007799500_829),
        .read_data(inj_read_data_1755007799505_257),
        .clk(clk),
        .read_address(inj_read_address_1755007799505_280),
        .rst(reset),
        .write_address(inj_write_address_1755007799505_176),
        .write_data(inj_in1_1755007799501_35)
    );
    // BEGIN: SimpleAssign_ts1755007799504
    assign inj_val_out_1755007799504_33 = inj_val_in_1755007799504_971;
    // END: SimpleAssign_ts1755007799504

    ModuleDefinition ModuleDefinition_inst_1755007799503_1359 (
        .in_md(clk),
        .out_md(inj_out_md_1755007799503_705)
    );
    // BEGIN: mod_casez_wildcard_ts1755007799502
always_comb begin
    casez (inj_in_mask_z_1755007799502_922)
        4'b10?0: begin
            inj_out_match_type_z_1755007799502_372 = 2'b00;
        end
        4'b011?: begin
            inj_out_match_type_z_1755007799502_372 = 2'b01;
        end
        default: begin
            inj_out_match_type_z_1755007799502_372 = 2'b11;
        end
    endcase
end
    // END: mod_casez_wildcard_ts1755007799502

    ModMultipleAlways ModMultipleAlways_inst_1755007799502_3351 (
        .din_a(inj_in_m_1755007799500_829),
        .din_b(inj_din_b_1755007799502_877),
        .rst_n(reset),
        .dout_a(inj_dout_a_1755007799502_253),
        .dout_b(inj_dout_b_1755007799502_316),
        .clk_a(clk),
        .clk_b(clk)
    );
    // BEGIN: remaining_reduction_ops_ts1755007799501
    assign inj_nand_out_1755007799501_704 = ~&inj_in1_1755007799501_35;
    assign inj_nor_out_1755007799501_709 = ~|inj_in2_1755007799501_589;
    assign inj_xnor_out_1755007799501_862 = ^~inj_in3_1755007799501_576;
    // END: remaining_reduction_ops_ts1755007799501

    // BEGIN: Comb_IfElse_ts1755007799501
    always_comb begin
        if (clk) begin
            inj_result_val_1755007799501_854 = inj_value1_1755007799501_997;
        end else begin
            inj_result_val_1755007799501_854 = inj_value2_1755007799501_576;
        end
    end
    // END: Comb_IfElse_ts1755007799501

    LintAsyncFovIssue LintAsyncFovIssue_inst_1755007799500_1641 (
        .out_i(inj_out_i_1755007799500_718),
        .clk(clk),
        .in_h(inj_in_m_1755007799500_829),
        .rst_n(reset)
    );
    LintParamUnused LintParamUnused_inst_1755007799500_2658 (
        .in_m(inj_in_m_1755007799500_829),
        .out_n(inj_out_n_1755007799500_493)
    );
    always_comb begin
        my_struct_var = inj_packed_in_1755007799500_506;
    end
    assign inj_field2_o_1755007799500_779 = my_struct_var.field2_ts1755007799500;
    // END: typedef_struct_mod_ts1755007799500

    assign inj_out_val_1755007799500_705 = inj_in_val_1755007799500_546;
    // END: undeclared_but_found_pkg_diag_mod_ts1755007799500
endmodule

