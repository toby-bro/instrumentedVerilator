module dup_cond (
    input logic [3:0] control,
    input logic [7:0] data_a,
    input logic [7:0] data_b,
    output logic [7:0] result1,
    output logic [7:0] result2
);
    always_comb begin
        result1 = '0;
        result2 = '0;
        if (control[0]) begin
            result1 = data_a + data_b;
        end else begin
            result1 = data_a - data_b;
        end
        if (control[1]) begin
            result2 = data_a - data_b;
        end else begin
            result2 = data_a + data_b;
        end
        case (control[3:2])
            2'b00: result1 = data_a & data_b;
            2'b01: result1 = data_a | data_b;
            2'b10: result2 = data_a & data_b;
            2'b11: result2 = data_a | data_b;
            default: begin result1 = '0; result2 = '0; end
        endcase
        if (control[0] == control[1]) begin
            result1 = result1 + 1;
        end else if (control[2] != control[3]) begin
            result2 = result2 - 1;
        end
    end
endmodule

module nested_blocks (
    input logic data_value,
    input logic level1_en,
    input logic level2_en,
    output logic result_out
);
    always_comb begin : main_block 
        result_out = 1'b0; 
        if (level1_en) begin : inner_block1 
            if (level2_en) begin : inner_block2 
                result_out = data_value;
            end 
        end 
    end
endmodule

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module virtual_interface_lookup_mod (
    input logic dummy_in,
    input logic [7:0] vif_data,
    input logic vif_valid,
    output logic dummy_out,
    output logic [7:0] out_data,
    output logic out_valid
);
    always_comb begin
        out_data  = vif_data;
        out_valid = vif_valid;
        dummy_out = dummy_in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007806741_36,
    input logic [3:0] inj_case_inside_val_1755007806741_327,
    input logic inj_condition_y_1755007806740_605,
    input logic [7:0] inj_data_b_1755007806742_279,
    input logic [31:0] inj_in_1755007806740_68,
    input logic [7:0] inj_in_val_y_1755007806740_836,
    input logic inj_level2_en_1755007806741_382,
    input logic inj_vif_valid_1755007806741_536,
    input wire reset,
    output logic [3:0] inj_data_out1_n_1755007806743_772,
    output logic [3:0] inj_data_out2_n_1755007806743_863,
    output logic inj_dummy_out_1755007806741_691,
    output logic [4:0] inj_internal_out_1755007806741_692,
    output logic [7:0] inj_out1_1755007806740_222,
    output logic inj_out2_1755007806740_532,
    output logic [7:0] inj_out_data_1755007806741_568,
    output logic [3:0] inj_out_narrow_1755007806744_92,
    output logic inj_out_valid_1755007806741_548,
    output logic [7:0] inj_out_vec_y_1755007806740_909,
    output logic [7:0] inj_result1_1755007806742_293,
    output logic [7:0] inj_result2_1755007806742_346,
    output logic inj_result_out_1755007806741_147
);
    // BEGIN: split_vector_assign_ts1755007806740
    // BEGIN: constant_sel_ts1755007806740
    // BEGIN: case_priority_casex_complex_mod_ts1755007806742
    // BEGIN: LintImplicitWidth_ts1755007806744
    assign inj_out_narrow_1755007806744_92 = inj_data_b_1755007806742_279;
    // END: LintImplicitWidth_ts1755007806744

    split_multiple_blocking split_multiple_blocking_inst_1755007806743_1304 (
        .data_in_n(inj_case_inside_val_1755007806741_327),
        .data_out1_n(inj_data_out1_n_1755007806743_772),
        .data_out2_n(inj_data_out2_n_1755007806743_863)
    );
    dup_cond dup_cond_inst_1755007806742_2023 (
        .control(inj_case_inside_val_1755007806741_327),
        .data_a(inj_in_val_y_1755007806740_836),
        .data_b(inj_data_b_1755007806742_279),
        .result1(inj_result1_1755007806742_293),
        .result2(inj_result2_1755007806742_346)
    );
    always @* begin
        priority casex ({inj_case_expr_1755007806741_36, inj_case_inside_val_1755007806741_327[1:0]})
            4'b1???: inj_internal_out_1755007806741_692 = 24;
            4'b?1??: inj_internal_out_1755007806741_692 = 25;  
            4'b??1?: inj_internal_out_1755007806741_692 = 26;  
            4'b???1: inj_internal_out_1755007806741_692 = 27;  
            4'b0000: inj_internal_out_1755007806741_692 = 28;  
            default: inj_internal_out_1755007806741_692 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755007806742

    nested_blocks nested_blocks_inst_1755007806741_2325 (
        .data_value(inj_condition_y_1755007806740_605),
        .level1_en(inj_vif_valid_1755007806741_536),
        .level2_en(inj_level2_en_1755007806741_382),
        .result_out(inj_result_out_1755007806741_147)
    );
    virtual_interface_lookup_mod virtual_interface_lookup_mod_inst_1755007806741_477 (
        .dummy_out(inj_dummy_out_1755007806741_691),
        .out_data(inj_out_data_1755007806741_568),
        .out_valid(inj_out_valid_1755007806741_548),
        .dummy_in(inj_condition_y_1755007806740_605),
        .vif_data(inj_in_val_y_1755007806740_836),
        .vif_valid(inj_vif_valid_1755007806741_536)
    );
    assign inj_out1_1755007806740_222 = inj_in_1755007806740_68[15:8];
    assign inj_out2_1755007806740_532 = inj_in_1755007806740_68[3];
    // END: constant_sel_ts1755007806740

    always @(posedge clk) begin
        if (inj_condition_y_1755007806740_605) begin
            inj_out_vec_y_1755007806740_909[3:0] <= inj_in_val_y_1755007806740_836[3:0];
            inj_out_vec_y_1755007806740_909[7:4] <= inj_in_val_y_1755007806740_836[7:4] + 1;
        end else begin
            inj_out_vec_y_1755007806740_909 <= 8'hFF;
        end
    end
    // END: split_vector_assign_ts1755007806740
endmodule

