module snippet (
    input wire clk,
    input logic [7:0] inj_byte_val_1755007914344_160,
    input logic [1:0] inj_case_expr_1755007914344_592,
    input logic inj_in1_1755007914345_190,
    input logic inj_in2_1755007914345_329,
    input logic [15:0] inj_packed_in_1755007914344_122,
    input wire reset,
    output logic [7:0] inj_byte_out_1755007914344_400,
    output logic [4:0] inj_internal_out_1755007914344_48,
    output logic inj_out_1755007914345_154,
    output logic [15:0] inj_packed_out_1755007914344_550
);
    // BEGIN: PackedStructOps_ts1755007914344
    typedef struct packed {
        logic [7:0] low_ts1755007914344;
        logic [7:0] high_ts1755007914344;
    } pair_t;
    pair_t data_pair;
    // BEGIN: simple_and_gate_ts1755007914345
    assign inj_out_1755007914345_154 = inj_in1_1755007914345_190 & inj_in2_1755007914345_329;
    // END: simple_and_gate_ts1755007914345

    // BEGIN: case_unique0_violating_mod_ts1755007914344
    always @* begin
        unique0 casez (inj_case_expr_1755007914344_592)
            2'b1?: inj_internal_out_1755007914344_48 = 8;
            2'b11: inj_internal_out_1755007914344_48 = 9;  
            2'b?1: inj_internal_out_1755007914344_48 = 10; 
            2'b00: inj_internal_out_1755007914344_48 = 11; 
        endcase
    end
    // END: case_unique0_violating_mod_ts1755007914344

    assign data_pair.high_ts1755007914344 = inj_packed_in_1755007914344_122[15:8];
    assign data_pair.low_ts1755007914344 = inj_byte_val_1755007914344_160;
    assign inj_byte_out_1755007914344_400 = data_pair.high_ts1755007914344;
    assign inj_packed_out_1755007914344_550[15:8] = data_pair.high_ts1755007914344;
    assign inj_packed_out_1755007914344_550[7:0] = data_pair.low_ts1755007914344 + inj_byte_val_1755007914344_160;
    // END: PackedStructOps_ts1755007914344
endmodule

