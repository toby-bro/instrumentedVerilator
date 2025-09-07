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
    input logic inj_data_value_1755004211091_726,
    input wire [3:0] inj_in0_1755004211091_617,
    input wire [3:0] inj_in1_1755004211091_69,
    input wire [3:0] inj_in2_1755004211091_25,
    input wire [3:0] inj_in3_1755004211091_540,
    input bit [3:0] inj_in_mask_x_1755004211091_629,
    input logic inj_level1_en_1755004211091_958,
    input logic inj_level2_en_1755004211091_505,
    input logic [4:0] inj_read_address_1755004211091_736,
    input wire [1:0] inj_sel_1755004211091_180,
    input logic [4:0] inj_write_address_1755004211091_291,
    input logic [7:0] inj_write_data_1755004211091_881,
    input wire reset,
    output reg [3:0] inj_mux_out_1755004211091_16,
    output bit [1:0] inj_out_match_type_x_1755004211091_777,
    output logic [7:0] inj_read_data_1755004211091_966,
    output logic inj_result_out_1755004211091_849
);
    // BEGIN: nested_blocks_ts1755004211091
    // BEGIN: mod_casex_wildcard_overlap_priority_ts1755004211092
always_comb begin
    inj_out_match_type_x_1755004211091_777 = 2'b01;
    priority casex (inj_in_mask_x_1755004211091_629)
        4'b1X0Z: begin
            inj_out_match_type_x_1755004211091_777 = 2'b10;
        end
        4'b10?Z: begin
            inj_out_match_type_x_1755004211091_777 = 2'b11;
        end
        4'bZ1?X: begin
            inj_out_match_type_x_1755004211091_777 = 2'b00;
        end
        default: begin
            inj_out_match_type_x_1755004211091_777 = 2'b01;
        end
    endcase
end
    // END: mod_casex_wildcard_overlap_priority_ts1755004211092

    Comb_Case Comb_Case_inst_1755004211091_8406 (
        .in1(inj_in1_1755004211091_69),
        .in2(inj_in2_1755004211091_25),
        .in3(inj_in3_1755004211091_540),
        .sel(inj_sel_1755004211091_180),
        .mux_out(inj_mux_out_1755004211091_16),
        .in0(inj_in0_1755004211091_617)
    );
    SynchronousMemory SynchronousMemory_inst_1755004211091_8525 (
        .write_data(inj_write_data_1755004211091_881),
        .write_en(inj_level1_en_1755004211091_958),
        .read_data(inj_read_data_1755004211091_966),
        .clk(clk),
        .read_address(inj_read_address_1755004211091_736),
        .rst(reset),
        .write_address(inj_write_address_1755004211091_291)
    );
    always_comb begin : main_block 
        inj_result_out_1755004211091_849 = 1'b0; 
        if (inj_level1_en_1755004211091_958) begin : inner_block1 
            if (inj_level2_en_1755004211091_505) begin : inner_block2 
                inj_result_out_1755004211091_849 = inj_data_value_1755004211091_726;
            end 
        end 
    end
    // END: nested_blocks_ts1755004211091
endmodule

