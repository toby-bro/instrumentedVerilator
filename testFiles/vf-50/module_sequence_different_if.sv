interface seq2_if;
    logic [7:0] status_byte;
    modport PortB (output status_byte);
endinterface
interface seq_if;
    logic [31:0] value_a;
    modport PortA (output value_a);
endinterface
module module_sequence_different_if (
    input wire clk,
    input logic [4:0] inj_index_1755538600933_304,
    input logic [31:0] inj_p_in2_1755538600933_960,
    input logic [1:0] inj_p_mode_1755538600933_935,
    input logic [31:0] input1,
    input logic [7:0] input2_byte,
    input wire rst,
    output logic [7:0] inj_final_result_1755538600933_932,
    output logic [31:0] inj_p_out_1755538600933_495,
    output logic sequence_valid
);
    // BEGIN: more_procedural_ts1755538600933
    // BEGIN: dup_literal_param_ts1755538600934
    parameter CONST_A = 8'd10;
    localparam CONST_B = 8'd20;
    parameter CONST_C = 10;
    localparam CONST_D = 8'hFF;
    parameter CONST_E = 8'b01010101;
    logic [7:0] temp1_ts1755538600934, temp2_ts1755538600934;
    assign temp1_ts1755538600934 = inj_index_1755538600933_304 + CONST_A;
    assign temp2_ts1755538600934 = inj_index_1755538600933_304 + 10;
    always_comb begin
        logic [7:0] local_temp_ts1755538600934;
        local_temp_ts1755538600934 = inj_index_1755538600933_304 * CONST_B;
        inj_final_result_1755538600933_932 = temp1_ts1755538600934 + temp2_ts1755538600934 + local_temp_ts1755538600934;
        if (inj_index_1755538600933_304 > 5) begin
            inj_final_result_1755538600933_932 = inj_final_result_1755538600933_932 + 1;
        end else if (inj_index_1755538600933_304 < CONST_C) begin
            inj_final_result_1755538600933_932 = inj_final_result_1755538600933_932 - 1;
        end
        case (inj_index_1755538600933_304)
            5'd0: inj_final_result_1755538600933_932 = CONST_A;
            5'd1: inj_final_result_1755538600933_932 = 20;
            5'd2: inj_final_result_1755538600933_932 = 10;
            5'd3: inj_final_result_1755538600933_932 = CONST_B;
            5'd4: inj_final_result_1755538600933_932 = CONST_D;
            5'd5: inj_final_result_1755538600933_932 = 8'hFF;
            default: inj_final_result_1755538600933_932 = CONST_E;
        endcase
    end
    // END: dup_literal_param_ts1755538600934

    always_comb begin
        case (inj_p_mode_1755538600933_935)
            2'b00: inj_p_out_1755538600933_495 = (input1 + inj_p_in2_1755538600933_960) * 2;
            2'b01: inj_p_out_1755538600933_495 = (input1 - inj_p_in2_1755538600933_960) / 3; 
            2'b10: inj_p_out_1755538600933_495 = (input1 << 4) | (inj_p_in2_1755538600933_960 >> 2);
            default: inj_p_out_1755538600933_495 = ~(input1 ^ inj_p_in2_1755538600933_960) + 1;
        endcase
    end
    // END: more_procedural_ts1755538600933

    seq_if sif_port();
    seq2_if sif2_port();
    always_comb begin
        sif_port.value_a = input1;
        sif2_port.status_byte = input2_byte;
        sequence_valid = 1'b1;
    end
endmodule

