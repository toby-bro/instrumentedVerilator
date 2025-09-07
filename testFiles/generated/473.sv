module typedef_struct_public_mod (
    input logic [15:0] packed_in,
    output logic [7:0] field2_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_public_packed_struct_t;
    my_public_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = packed_in;
    end
    assign field2_o = my_struct_var.field2;
endmodule

module used_before_declared_diag_mod (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] undeclared_var_ubddm = 8'd5;
    assign out_val = in_val + undeclared_var_ubddm;
endmodule

module snippet (
    input wire clk,
    input logic inj_c1_x_1755007912322_34,
    input logic inj_c2_x_1755007912322_832,
    input logic inj_c3_x_1755007912322_480,
    input logic [7:0] inj_in_val_1755007912322_751,
    input logic [15:0] inj_packed_in_1755007912322_390,
    input logic [7:0] inj_v2_x_1755007912322_21,
    input logic [7:0] inj_v3_x_1755007912322_135,
    input logic [7:0] inj_v4_x_1755007912322_307,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007912322_295,
    output logic inj_out_sub_1755007912322_991,
    output logic [7:0] inj_out_val_1755007912322_409,
    output logic [7:0] inj_out_x_1755007912322_945
);
    // BEGIN: split_ifelse_chain_ts1755007912322
    // BEGIN: mod_sub_ts1755007912322
    assign inj_out_sub_1755007912322_991 = reset;
    // END: mod_sub_ts1755007912322

    always @(posedge clk) begin
        if (inj_c1_x_1755007912322_34) begin
            inj_out_x_1755007912322_945 <= inj_in_val_1755007912322_751;
        end else if (inj_c2_x_1755007912322_832) begin
            inj_out_x_1755007912322_945 <= inj_v2_x_1755007912322_21;
        end else if (inj_c3_x_1755007912322_480) begin
            inj_out_x_1755007912322_945 <= inj_v3_x_1755007912322_135;
        end else begin
            inj_out_x_1755007912322_945 <= inj_v4_x_1755007912322_307;
        end
    end
    // END: split_ifelse_chain_ts1755007912322

    used_before_declared_diag_mod used_before_declared_diag_mod_inst_1755007912322_9551 (
        .in_val(inj_in_val_1755007912322_751),
        .out_val(inj_out_val_1755007912322_409)
    );
    typedef_struct_public_mod typedef_struct_public_mod_inst_1755007912322_7643 (
        .field2_o(inj_field2_o_1755007912322_295),
        .packed_in(inj_packed_in_1755007912322_390)
    );
endmodule

