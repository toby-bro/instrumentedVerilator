module system_names_mod (
    input int in_val,
    output int out_val
);
    assign out_val = $bits(in_val);
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_in_vec_1755007788012_792,
    input int inj_index_in_1755007788012_818,
    input wire reset,
    output logic inj_out_bit_1755007788012_742,
    output logic [3:0] inj_out_slice_1755007788012_490,
    output int inj_out_val_1755007788012_997
);
    // BEGIN: element_select_packed_ts1755007788012
    system_names_mod system_names_mod_inst_1755007788012_4804 (
        .in_val(inj_index_in_1755007788012_818),
        .out_val(inj_out_val_1755007788012_997)
    );
    always_comb begin
        if (inj_index_in_1755007788012_818 >= 0 && inj_index_in_1755007788012_818 < 8)
            inj_out_bit_1755007788012_742 = inj_in_vec_1755007788012_792[inj_index_in_1755007788012_818];
        else
            inj_out_bit_1755007788012_742 = 'x; 
    end
    assign inj_out_slice_1755007788012_490 = inj_in_vec_1755007788012_792[6:3];
    // END: element_select_packed_ts1755007788012
endmodule

