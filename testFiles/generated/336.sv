module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007867029_313,
    input logic [3:0] inj_case_inside_val_1755007867029_79,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007867029_346,
    output wire inj_match_x_neq_1755007867029_269,
    output wire inj_match_z_eq_1755007867029_337,
    inout wire [3:0] inj_data_io_1755007867029_945
);
    // BEGIN: CaseEq_ts1755007867029
    // BEGIN: case_unique_casez_reordered_mod_ts1755007867030
    always @* begin
        unique casez ({inj_case_expr_1755007867029_313[0], inj_case_inside_val_1755007867029_79[3:2], inj_case_expr_1755007867029_313[1]})
            4'b1?0?: inj_internal_out_1755007867029_346 = 30;
            4'b?101: inj_internal_out_1755007867029_346 = 31;  
            4'b0?1?: inj_internal_out_1755007867029_346 = 32;
            4'b1?1?: inj_internal_out_1755007867029_346 = 33;  
            4'b?111: inj_internal_out_1755007867029_346 = 34;  
        endcase
    end
    // END: case_unique_casez_reordered_mod_ts1755007867030

    assign inj_match_z_eq_1755007867029_337 = (inj_data_io_1755007867029_945 === 4'b101z);
    assign inj_match_x_neq_1755007867029_269 = (inj_data_io_1755007867029_945 !== 4'b1x0x);
    // END: CaseEq_ts1755007867029
endmodule

