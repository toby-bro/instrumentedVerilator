module dup_logic_ops (
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] d3,
    input logic [3:0] flags,
    output logic [7:0] out1
);
    logic cond1, cond2, cond3;
    logic complex_cond1, complex_cond2;
    assign cond1 = flags[0] && flags[1];
    assign cond2 = flags[2] || flags[3];
    assign cond3 = !flags[0];
    assign complex_cond1 = (cond1 || cond2) && cond3;
    assign complex_cond2 = !(flags[0] && flags[1]) || (flags[2] || !flags[3]);
    always_comb begin
        out1 = '0;
        if (complex_cond1) begin
            out1 = d1 + d2;
        end else begin
            out1 = d1 ^ d3;
        end
        if (complex_cond2) begin
            out1 = out1 + d3;
        end else begin
            out1 = out1 - d3;
        end
        if ((flags[0] && flags[1]) && (!flags[2] || flags[3])) begin
            out1 = out1 * 2;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_d1_1755007793054_495,
    input logic [7:0] inj_d2_1755007793054_422,
    input logic [7:0] inj_d3_1755007793054_741,
    input wire [3:0] inj_data_in_1755007793054_131,
    input logic [3:0] inj_flags_1755007793054_834,
    input logic inj_fs_in_target_1755007793054_656,
    input int inj_val_in_1755007793055_483,
    input wire reset,
    output reg [3:0] inj_data_out_1755007793054_225,
    output int inj_driven_var_1755007793055_593,
    output logic inj_fs_out_target_1755007793054_963,
    output logic [7:0] inj_out1_1755007793054_230
);
    // BEGIN: mod_event_implicit_ts1755007793054
    // BEGIN: mod_fixup_target_ts1755007793054
    // BEGIN: m_driver_check_ts1755007793055
    int my_driven_var_ts1755007793055;
    function automatic void write_to_var(input int val);
        my_driven_var_ts1755007793055 = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(inj_val_in_1755007793055_483);
    end
    assign inj_driven_var_1755007793055_593 = my_driven_var_ts1755007793055;
    // END: m_driver_check_ts1755007793055

    assign inj_fs_out_target_1755007793054_963 = inj_fs_in_target_1755007793054_656;
    // END: mod_fixup_target_ts1755007793054

    dup_logic_ops dup_logic_ops_inst_1755007793054_2603 (
        .flags(inj_flags_1755007793054_834),
        .out1(inj_out1_1755007793054_230),
        .d1(inj_d1_1755007793054_495),
        .d2(inj_d2_1755007793054_422),
        .d3(inj_d3_1755007793054_741)
    );
    always @* begin
        inj_data_out_1755007793054_225 = inj_data_in_1755007793054_131;
    end
    // END: mod_event_implicit_ts1755007793054
endmodule

