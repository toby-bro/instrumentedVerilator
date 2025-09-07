module snippet (
    input wire clk,
    input logic inj_lc_en_1755007767045_179,
    input wire reset,
    output logic [15:0] inj_lc_val_1755007767045_715
);
    // BEGIN: macro_line_continuation_user_ts1755007767045
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg_ts1755007767045;
    always_comb begin
        if (inj_lc_en_1755007767045_179)
            value_reg_ts1755007767045 = `MULTI_VAL;
        else
            value_reg_ts1755007767045 = `ADD_FIVE(16'h0010);
    end
    assign inj_lc_val_1755007767045_715 = value_reg_ts1755007767045;
    // END: macro_line_continuation_user_ts1755007767045
endmodule

