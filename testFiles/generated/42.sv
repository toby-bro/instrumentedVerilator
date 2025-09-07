module non_ansi_basic (
    non_ansi_a,
    non_ansi_basic_input,
    non_ansi_b,
    non_ansi_basic_output
);
    input wire non_ansi_a;
    output reg non_ansi_b;
    input logic non_ansi_basic_input;
    output logic non_ansi_basic_output;
    always_comb begin
        non_ansi_b = non_ansi_a;
        non_ansi_basic_output = non_ansi_basic_input;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755004217554_41,
    input int inj_b_1755004217554_73,
    input bit inj_cfg_in_1755004217555_888,
    input wire reset,
    output bit inj_cfg_out_1755004217555_321,
    output reg inj_non_ansi_b_1755004217556_172,
    output logic inj_non_ansi_basic_output_1755004217556_470,
    output logic [31:0] inj_out1_1755004217555_299,
    output logic inj_out_a_1755004217554_334,
    output int inj_out_b_1755004217554_452
);
    // BEGIN: ModuleBasic_ts1755004217555
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c_ts1755004217554;
    int   d_ts1755004217554;
    always_comb begin
        logic temp_v_ts1755004217554;
            non_ansi_basic non_ansi_basic_inst_1755004217556_8896 (
                .non_ansi_b(inj_non_ansi_b_1755004217556_172),
                .non_ansi_basic_input(c_ts1755004217554),
                .non_ansi_basic_output(inj_non_ansi_basic_output_1755004217556_470),
                .non_ansi_a(clk)
            );
            // BEGIN: simple_macro_user_ts1755004217555
            `define SIMPLE_VALUE 32'd12345
            `define ANOTHER_SIMPLE (1 + 2)
            assign inj_out1_1755004217555_299 = c_ts1755004217554 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
            // END: simple_macro_user_ts1755004217555

            // BEGIN: Module_ConfigKeywords_ts1755004217555
            assign inj_cfg_out_1755004217555_321 = inj_cfg_in_1755004217555_888;
            // END: Module_ConfigKeywords_ts1755004217555

        temp_v_ts1755004217554 = d_ts1755004217554;
        c_ts1755004217554      = temp_v_ts1755004217554;
    end
    assign inj_out_a_1755004217554_334 = inj_a_1755004217554_41;
    assign d_ts1755004217554     = inj_b_1755004217554_73;
    assign inj_out_b_1755004217554_452 = d_ts1755004217554 + P1 + LP1;
    // END: ModuleBasic_ts1755004217555
endmodule

