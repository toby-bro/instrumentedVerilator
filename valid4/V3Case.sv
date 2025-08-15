module SimpleCase_Mux (
    input logic [3:0] in_select,
    input logic [7:0] in_data0,
    input logic [7:0] in_data1,
    input logic [7:0] in_data2,
    input logic [7:0] in_data3,
    output logic [7:0] out_muxed_data
);
    logic [7:0] local_result;
    always_comb begin : case_mux_block
        case (in_select)
            4'h0: local_result = in_data0;
            4'h1: local_result = in_data1;
            4'h2: local_result = in_data2;
            4'h3: local_result = in_data3;
            default: local_result = 8'hFF;
        endcase
    end
    assign out_muxed_data = local_result;
endmodule
module CaseOverlap_Priority (
    input logic [3:0] in_val,
    output logic [7:0] out_overlap_result,
    output logic [7:0] out_priority_result
);
    logic [7:0] overlap_reg;
    logic [7:0] priority_reg;
    always_comb begin : overlap_casex_block
        casex (in_val) 
            4'b000?: overlap_reg = 8'hAA;
            4'b00?0: overlap_reg = 8'hBB;
            4'b0?00: overlap_reg = 8'hCC;
            4'b?000: overlap_reg = 8'hDD;
            default: overlap_reg = 8'hFF;
        endcase
    end
    always_comb begin : priority_casex_block
        priority casex (in_val) 
            4'b000?: priority_reg = 8'hAA;
            4'b00?0: priority_reg = 8'hBB;
            4'b0?00: priority_reg = 8'hCC;
            4'b?000: priority_reg = 8'hDD;
            default: priority_reg = 8'hEE;
        endcase
    end
    assign out_overlap_result = overlap_reg;
    assign out_priority_result = priority_reg;
endmodule
module CaseXYZ_Values (
    input logic [3:0] in_test_val,
    output logic [7:0] out_casex_result,
    output logic [7:0] out_casez_result,
    output logic [7:0] out_case_result
);
    logic [7:0] casex_reg;
    logic [7:0] casez_reg;
    logic [7:0] case_reg;
    always_comb begin : casex_block
        casex (in_test_val)
            4'b101?: casex_reg = 8'h0A; 
            4'b1?10: casex_reg = 8'h0B; 
            default: casex_reg = 8'hFF;
        endcase
    end
    always_comb begin : casez_block
        casez (in_test_val)
            4'b101?: casez_reg = 8'h1A; 
            4'b1Z10: casez_reg = 8'h1B;
            4'b0?01: casez_reg = 8'h1C;
            default: casez_reg = 8'hFF;
        endcase
    end
    always_comb begin : plain_casex_block
        casex (in_test_val) 
            4'b101?: case_reg = 8'h2A; 
            4'b0?01: case_reg = 8'h2B;
            default: case_reg = 8'hFF;
        endcase
    end
    assign out_casex_result = casex_reg;
    assign out_casez_result = casez_reg;
    assign out_case_result = case_reg;
endmodule
module EnumCase_Completeness (
    input MyEnum in_enum_val,
    output logic [7:0] out_enum_covered_result,
    output logic [7:0] out_enum_incomplete_result
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_RUN,
        STATE_PAUSE,
        STATE_DONE
    } MyEnum;
    logic [7:0] covered_reg;
    logic [7:0] incomplete_reg;
    always_comb begin : enum_covered_block
        unique case (in_enum_val)
            STATE_IDLE:  covered_reg = 8'hC0;
            STATE_RUN:   covered_reg = 8'hC1;
            STATE_PAUSE: covered_reg = 8'hC2;
            STATE_DONE:  covered_reg = 8'hC3;
        endcase
    end
    always_comb begin : enum_incomplete_block
        unique0 case (in_enum_val)
            STATE_IDLE:  incomplete_reg = 8'h10;
            STATE_RUN:   incomplete_reg = 8'h11;
            STATE_PAUSE: incomplete_reg = 8'h12;
        endcase
    end
    assign out_enum_covered_result = covered_reg;
    assign out_enum_incomplete_result = incomplete_reg;
endmodule
module ComplexCase_Range_Inside (
    input logic [31:0] in_wide_val,
    input logic [7:0] in_small_val,
    output logic [7:0] out_range_result,
    output logic [7:0] out_inside_result,
    output logic [7:0] out_wide_result,
    output logic [7:0] out_expr_result
);
    logic [7:0] range_reg;
    logic [7:0] inside_reg;
    logic [7:0] wide_reg;
    logic [7:0] expr_reg;
    always_comb begin : range_case_block
        case (in_small_val) inside
            8'h00:                  range_reg = 8'h00;
            8'h01:                  range_reg = 8'h01;
            [8'h02:8'h05]:          range_reg = 8'h02;
            8'h06:                  range_reg = 8'h06;
            [8'h07:8'h0A]:          range_reg = 8'h07;
            default:                range_reg = 8'hF0;
        endcase
    end
    always_comb begin : inside_case_block
        case (in_small_val) inside
            8'h00:                  inside_reg = 8'h00;
            8'h01:                  inside_reg = 8'h01;
            [8'h02:8'h05], 8'h07:   inside_reg = 8'h03;
            8'h06:                  inside_reg = 8'h06;
            default:                inside_reg = 8'hF0;
        endcase
    end
    always_comb begin : wide_case_block
        case (in_wide_val)
            32'h00000000: wide_reg = 8'h00;
            32'h00000001: wide_reg = 8'h01;
            32'hFFFFFFFF: wide_reg = 8'hF0;
            default:      wide_reg = 8'hE0;
        endcase
    end
    always_comb begin : expr_case_block
        case (in_small_val)
            8'h00:   expr_reg = 8'h00;
            8'h01:   expr_reg = 8'h01;
            8'h02:   expr_reg = 8'h02;
            8'h03:   expr_reg = 8'h03;
            default: expr_reg = 8'hF0;
        endcase
    end
    assign out_range_result = range_reg;
    assign out_inside_result = inside_reg;
    assign out_wide_result = wide_reg;
    assign out_expr_result = expr_reg;
endmodule
module CaseMultipleDefault (
    input logic [1:0] in_sel,
    output logic [7:0] out_result
);
    logic [7:0] reg_result;
    always_comb begin : multi_default_block
        case (in_sel)
            2'b00: reg_result = 8'hA0;
            2'b01: reg_result = 8'hA1;
            default: reg_result = 8'hFF;
        endcase
    end
    assign out_result = reg_result;
endmodule
module GenerateCaseTest (
    input logic [7:0] in_data_g,
    output logic [7:0] out_data_g
);
    parameter P_SEL = 4'b0001; 
    logic [7:0] gen_result;
    generate
        case (P_SEL)
            4'b0001: begin : gen_block_1
                always_comb begin
                    gen_result = in_data_g + 8'h01;
                end
            end
            4'b1011: begin : gen_block_2
                always_comb begin
                    gen_result = in_data_g + 8'h02;
                end
            end
            default: begin : gen_block_default
                always_comb begin
                    gen_result = in_data_g + 8'h03;
                end
            end
        endcase
    endgenerate
    assign out_data_g = gen_result;
endmodule
