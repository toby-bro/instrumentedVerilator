module module_concat_if (
    input wire [3:0] in_a,
    input wire [3:0] in_b,
    input wire [7:0] in_c,
    input wire in_cond_if,
    output logic [15:0] out_concat,
    output logic [7:0] out_if_else
);
    always_comb begin
    out_concat = {in_a, in_b, in_c};
    if (in_cond_if) begin
        out_if_else = in_c;
    end else begin
        out_if_else = {in_a, in_b};
    end
    end
endmodule

module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module snippet (
    input wire clk,
    input int inj_dummy_in_1755007888947_76,
    input wire [3:0] inj_in_a_1755007888946_370,
    input wire [3:0] inj_in_b_1755007888946_318,
    input wire [7:0] inj_in_c_1755007888946_973,
    input wire reset,
    output logic [15:0] inj_out_concat_1755007888946_502,
    output logic [7:0] inj_out_if_else_1755007888946_747,
    output int inj_out_val_1755007888947_962
);
    recursive_param_diag_mod recursive_param_diag_mod_inst_1755007888947_3698 (
        .dummy_in(inj_dummy_in_1755007888947_76),
        .out_val(inj_out_val_1755007888947_962)
    );
    module_concat_if module_concat_if_inst_1755007888946_2658 (
        .out_concat(inj_out_concat_1755007888946_502),
        .out_if_else(inj_out_if_else_1755007888946_747),
        .in_a(inj_in_a_1755007888946_370),
        .in_b(inj_in_b_1755007888946_318),
        .in_c(inj_in_c_1755007888946_973),
        .in_cond_if(reset)
    );
endmodule

