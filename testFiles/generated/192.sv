module macro_line_continuation_user (
    input logic lc_en,
    output logic [15:0] lc_val
);
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg;
    always_comb begin
        if (lc_en)
            value_reg = `MULTI_VAL;
        else
            value_reg = `ADD_FIVE(16'h0010);
    end
    assign lc_val = value_reg;
endmodule

module snippet (
    input wire clk,
    input logic inj_lc_en_1755007817312_704,
    input wire reset,
    output logic [15:0] inj_lc_val_1755007817312_430
);
    macro_line_continuation_user macro_line_continuation_user_inst_1755007817312_9874 (
        .lc_en(inj_lc_en_1755007817312_704),
        .lc_val(inj_lc_val_1755007817312_430)
    );
endmodule

