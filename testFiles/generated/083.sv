module snippet (
    input wire clk,
    input logic [15:0] inj_packed_in_1755007779799_694,
    input wire reset,
    output logic [7:0] inj_field2_o_1755007779799_3
);
    // BEGIN: typedef_struct_mod_ts1755007779800
    typedef struct packed {
        logic [7:0] field1_ts1755007779800;
        logic [7:0] field2_ts1755007779800;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    always_comb begin
        my_struct_var = inj_packed_in_1755007779799_694;
    end
    assign inj_field2_o_1755007779799_3 = my_struct_var.field2_ts1755007779800;
    // END: typedef_struct_mod_ts1755007779800
endmodule

