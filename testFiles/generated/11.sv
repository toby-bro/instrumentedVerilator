module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case_case,
    output logic [3:0] out_case_casex,
    output logic [3:0] out_case_casez
);
    always_comb begin
        case (selector)
            2'b00: out_case_case = data_c;
            2'b01: out_case_case = data_c + 1;
            2'b10: out_case_case = data_c + 2;
            default: out_case_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case_casez = data_c + 10;
            2'b1?: out_case_casez = data_c + 20;
            default: out_case_casez = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case_casex = data_c - 1;
            2'b1?: out_case_casex = data_c - 2;
            default: out_case_casex = 4'bxxxx;
        endcase
    end
endmodule

module Mod_BasicOps (
    input wire [7:0] in_a,
    input wire [7:0] in_b,
    input wire in_bit,
    input wire [7:0] in_c,
    input wire [7:0] in_const1,
    input wire [7:0] in_const2,
    output logic [7:0] out_add_assoc,
    output logic [7:0] out_and_assoc,
    output logic [7:0] out_and_swap_const,
    output logic [7:0] out_arith,
    output logic [7:0] out_bitwise,
    output logic out_logical,
    output logic [7:0] out_mul_assoc,
    output logic [7:0] out_negate,
    output logic [7:0] out_or_assoc,
    output logic [7:0] out_or_swap_not,
    output logic [7:0] out_unary_not,
    output logic [7:0] out_xor_assoc,
    output logic [7:0] out_xor_swap_var
);
    logic [7:0] intermediate_arith;
    logic [7:0] intermediate_bitwise;
    logic [0:0] intermediate_logical;
    logic [7:0] intermediate_add_assoc;
    logic [7:0] intermediate_mul_assoc;
    logic [7:0] intermediate_and_assoc;
    logic [7:0] intermediate_or_assoc;
    logic [7:0] intermediate_xor_assoc;
    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith = in_a;
        intermediate_arith = intermediate_arith + in_b;
        intermediate_arith = intermediate_arith - in_c;
        intermediate_arith = intermediate_arith * in_const1;
        if (in_b != CONST_ZERO) begin
            intermediate_arith = intermediate_arith / in_b;
            intermediate_arith = intermediate_arith % in_b;
        end else begin
            intermediate_arith = 'x;
        end
        out_arith = intermediate_arith;
        intermediate_bitwise = in_a;
        intermediate_bitwise = intermediate_bitwise & in_b;
        intermediate_bitwise = intermediate_bitwise | in_c;
        intermediate_bitwise = intermediate_bitwise ^ in_const1;
        out_bitwise = intermediate_bitwise;
        intermediate_logical = (in_a != CONST_ZERO) && (in_b != CONST_ZERO);
        intermediate_logical = intermediate_logical || (in_c != CONST_ZERO);
        out_logical = !intermediate_logical;
        out_unary_not = ~in_a;
        out_negate = -in_a;
        intermediate_add_assoc = (in_a + in_b) + in_c;
        out_add_assoc = intermediate_add_assoc;
        intermediate_mul_assoc = (in_a * in_b) * in_c;
        out_mul_assoc = intermediate_mul_assoc;
        intermediate_and_assoc = (in_a & in_b) & in_c;
        out_and_assoc = intermediate_and_assoc;
        intermediate_or_assoc = (in_a | in_b) | in_c;
        out_or_assoc = intermediate_or_assoc;
        intermediate_xor_assoc = (in_a ^ in_b) ^ in_c;
        out_xor_assoc = intermediate_xor_assoc;
        out_and_swap_const = in_const1 & in_a;
        out_or_swap_not = (~in_a) | in_b;
        out_xor_swap_var = in_b ^ in_c;
    end
endmodule

module formatting_stress (
    input logic [1:0] case_sel_fmt,
    input logic [7:0] data_in_fmt,
    input logic enable_block_fmt,
    input logic sel_fmt,
    output logic [7:0] data_out_fmt
);
    logic [7:0] temp_reg_fmt; 
    always_comb begin : stress_comb_block_label 
        data_out_fmt = 8'hXX; 
        if (enable_block_fmt) begin
            if (sel_fmt) begin
                case (case_sel_fmt) 
                    2'b00: data_out_fmt = data_in_fmt;
                    2'b01: begin 
                        data_out_fmt = ~data_in_fmt; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val; 
                        added_val = data_in_fmt + 8'h01; 
                        data_out_fmt = added_val; 
                        end 
                    default: data_out_fmt = 8'hFF; 
                endcase 
            end else begin
                data_out_fmt = data_in_fmt - 8'h01; 
            end 
        end else begin
            data_out_fmt = 8'h00; 
        end 
    end
endmodule

module generate_for_block (
    input logic [1:0] selector,
    output logic [7:0] selected_output
);
    wire [7:0] data [3:0]; 
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : data_gen
            assign data[i] = 8'(i + 1) * 8'(i + 1);
        end
    endgenerate
    always_comb begin
        case (selector)
            0: selected_output = data[0];
            1: selected_output = data[1];
            2: selected_output = data[2];
            3: selected_output = data[3];
            default: selected_output = 8'hXX;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_c_1755004206614_990,
    input bit inj_enable_in_1755004206622_833,
    input wire [7:0] inj_in_a_1755004206616_363,
    input wire [7:0] inj_in_b_1755004206616_219,
    input wire [7:0] inj_in_c_1755004206616_161,
    input wire [7:0] inj_in_const1_1755004206616_719,
    input wire [7:0] inj_in_const2_1755004206616_809,
    input logic [4:0] inj_read_address_1755004206615_678,
    input logic inj_sel_fmt_1755004206617_672,
    input logic [1:0] inj_selector_1755004206614_766,
    input wire [1:0] inj_selector_1755004206614_965,
    input logic [4:0] inj_write_address_1755004206615_851,
    input logic [7:0] inj_write_data_1755004206615_786,
    input logic inj_write_en_1755004206615_302,
    input wire reset,
    output logic [7:0] inj_data_out_fmt_1755004206617_702,
    output logic [7:0] inj_out_1755004206619_892,
    output bit inj_out_1755004206622_195,
    output logic [7:0] inj_out_add_assoc_1755004206616_862,
    output logic [7:0] inj_out_and_assoc_1755004206616_462,
    output logic [7:0] inj_out_and_swap_const_1755004206616_764,
    output logic [7:0] inj_out_arith_1755004206616_675,
    output logic [7:0] inj_out_bitwise_1755004206616_162,
    output logic [3:0] inj_out_case_case_1755004206614_10,
    output logic [3:0] inj_out_case_casex_1755004206614_138,
    output logic [3:0] inj_out_case_casez_1755004206614_629,
    output logic inj_out_logical_1755004206616_156,
    output logic inj_out_md_1755004206614_459,
    output logic [7:0] inj_out_mul_assoc_1755004206616_620,
    output logic [7:0] inj_out_negate_1755004206616_427,
    output logic [7:0] inj_out_or_assoc_1755004206616_178,
    output logic [7:0] inj_out_or_swap_not_1755004206616_973,
    output logic [7:0] inj_out_unary_not_1755004206616_178,
    output logic [7:0] inj_out_xor_assoc_1755004206616_930,
    output logic [7:0] inj_out_xor_swap_var_1755004206616_371,
    output logic [7:0] inj_read_data_1755004206615_343,
    output logic [7:0] inj_selected_output_1755004206614_886,
    output logic inj_sub_out_1755004206621_523
);
    // BEGIN: ModuleDefinition_ts1755004206614
    // BEGIN: SynchronousMemory_ts1755004206615
    logic [7:0] mem_ts1755004206615 [0:31];
        // BEGIN: mod_default_disable_ts1755004206622
        assign inj_out_1755004206622_195 = inj_enable_in_1755004206622_833;
        // END: mod_default_disable_ts1755004206622

        // BEGIN: sub_module_ts1755004206621
        assign inj_sub_out_1755004206621_523 = !inj_sel_fmt_1755004206617_672;
        // END: sub_module_ts1755004206621

        // BEGIN: timed_assign_unhandled_ts1755004206619
        always @(posedge clk) begin
            inj_out_1755004206619_892 <= mem_ts1755004206615;
        end
        // END: timed_assign_unhandled_ts1755004206619

        formatting_stress formatting_stress_inst_1755004206617_6846 (
            .sel_fmt(inj_sel_fmt_1755004206617_672),
            .data_out_fmt(inj_data_out_fmt_1755004206617_702),
            .case_sel_fmt(inj_selector_1755004206614_766),
            .data_in_fmt(inj_write_data_1755004206615_786),
            .enable_block_fmt(inj_write_en_1755004206615_302)
        );
        Mod_BasicOps Mod_BasicOps_inst_1755004206616_3605 (
            .out_xor_swap_var(inj_out_xor_swap_var_1755004206616_371),
            .out_bitwise(inj_out_bitwise_1755004206616_162),
            .in_a(inj_in_a_1755004206616_363),
            .out_negate(inj_out_negate_1755004206616_427),
            .out_unary_not(inj_out_unary_not_1755004206616_178),
            .out_arith(inj_out_arith_1755004206616_675),
            .in_c(inj_in_c_1755004206616_161),
            .in_b(inj_in_b_1755004206616_219),
            .out_and_assoc(inj_out_and_assoc_1755004206616_462),
            .out_or_swap_not(inj_out_or_swap_not_1755004206616_973),
            .in_bit(clk),
            .in_const1(inj_in_const1_1755004206616_719),
            .out_logical(inj_out_logical_1755004206616_156),
            .out_xor_assoc(inj_out_xor_assoc_1755004206616_930),
            .out_mul_assoc(inj_out_mul_assoc_1755004206616_620),
            .out_add_assoc(inj_out_add_assoc_1755004206616_862),
            .out_or_assoc(inj_out_or_assoc_1755004206616_178),
            .out_and_swap_const(inj_out_and_swap_const_1755004206616_764),
            .in_const2(inj_in_const2_1755004206616_809)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755004206615_343 <= 8'h0;
        end else begin
            if (inj_write_en_1755004206615_302) begin
                mem_ts1755004206615[inj_write_address_1755004206615_851] <= inj_write_data_1755004206615_786;
            end
            inj_read_data_1755004206615_343 <= mem_ts1755004206615[inj_read_address_1755004206615_678];
        end
    end
    // END: SynchronousMemory_ts1755004206615

    generate_for_block generate_for_block_inst_1755004206614_2025 (
        .selector(inj_selector_1755004206614_766),
        .selected_output(inj_selected_output_1755004206614_886)
    );
    assign inj_out_md_1755004206614_459 = clk;
    // END: ModuleDefinition_ts1755004206614

    CaseStatementConditions CaseStatementConditions_inst_1755004206614_1786 (
        .out_case_casez(inj_out_case_casez_1755004206614_629),
        .out_case_casex(inj_out_case_casex_1755004206614_138),
        .data_c(inj_data_c_1755004206614_990),
        .selector(inj_selector_1755004206614_965),
        .out_case_case(inj_out_case_case_1755004206614_10)
    );
endmodule

