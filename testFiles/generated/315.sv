interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
module FunctionTaskMod (
    input logic [7:0] data_in,
    output logic is_even
);
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp;
        tmp = v;
    endtask
    assign is_even = check_even(data_in);
endmodule

module param_local_port #(
    parameter int P_PORT_VAL = 25
) (
    input logic i_reset,
    output logic [7:0] o_sum
);
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    always_comb begin
        if (i_reset) begin
            o_sum = 0;
        end else begin
            o_sum = LP_CALCULATED;
        end
    end
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_a_1755007860403_653,
    input wire [1:0] inj_byte_idx_1755007860407_931,
    input logic [15:0] inj_data0_1755007860403_427,
    input logic [15:0] inj_data1_1755007860403_904,
    input bit [7:0] inj_data_in_1755007860403_19,
    input wire [15:0] inj_i_packed_data_1755007860404_92,
    input logic [2:0] inj_in_val_1755007860408_766,
    input logic inj_sel_1755007860403_523,
    input bit inj_select_signal_1755007860403_906,
    input wire [31:0] inj_wide_data_1755007860407_934,
    input wire reset,
    output logic [15:0] inj_data_out_1755007860403_600,
    output bit [7:0] inj_data_out_1755007860403_824,
    output logic inj_data_out_1755007860406_181,
    output logic inj_is_even_1755007860406_652,
    output logic [7:0] inj_o_member_sum_1755007860404_445,
    output logic [7:0] inj_o_sum_1755007860403_940,
    output logic inj_o_sum_1755007860405_157,
    output logic [7:0] inj_out_1755007860404_571,
    output logic inj_out_data_pull0_1755007860405_693,
    output logic inj_out_data_pull1_1755007860405_565,
    output reg inj_out_res_1755007860408_164,
    output reg [7:0] inj_selected_byte_1755007860407_873,
    output logic inj_valid_out_1755007860404_13,
    output logic [7:0] inj_wide_reg_1755007860405_619,
    output logic [3:0] inj_y_1755007860403_281
);
    // BEGIN: AlwaysCombInvert_ts1755007860403
    // BEGIN: CombinationalLogicExplicit_ts1755007860403
    // BEGIN: SimpleLogicTest_ts1755007860403
    logic [7:0] temp_data_ts1755007860403;
        // BEGIN: mod_lint_target_ts1755007860405
        logic l_reg_ts1755007860405;
            // BEGIN: casez_xz_alt_ts1755007860408
            always_comb begin
                inj_out_res_1755007860408_164 = 1'b0;
                casez (inj_in_val_1755007860408_766)
                    3'b1?z: inj_out_res_1755007860408_164 = 1'b1;
                    3'b0z?: inj_out_res_1755007860408_164 = 1'b0;
                    default: inj_out_res_1755007860408_164 = 1'b1;
                endcase
            end
            // END: casez_xz_alt_ts1755007860408

            // BEGIN: Bit_Manip_ts1755007860407
            always_comb begin
                case (inj_byte_idx_1755007860407_931)
                    2'b00: inj_selected_byte_1755007860407_873 = inj_wide_data_1755007860407_934[7:0];
                    2'b01: inj_selected_byte_1755007860407_873 = inj_wide_data_1755007860407_934[15:8];
                    2'b10: inj_selected_byte_1755007860407_873 = inj_wide_data_1755007860407_934[23:16];
                    default: inj_selected_byte_1755007860407_873 = inj_wide_data_1755007860407_934[31:24];
                endcase
            end
            // END: Bit_Manip_ts1755007860407

            FunctionTaskMod FunctionTaskMod_inst_1755007860406_6677 (
                .data_in(temp_data_ts1755007860403),
                .is_even(inj_is_even_1755007860406_652)
            );
            sequential_register sequential_register_inst_1755007860406_4653 (
                .enable_in(inj_sel_1755007860403_523),
                .reset_n(reset),
                .data_out(inj_data_out_1755007860406_181),
                .clk(clk),
                .data_in(l_reg_ts1755007860405)
            );
            // BEGIN: module_with_unconnected_drive_ts1755007860405
            assign inj_out_data_pull1_1755007860405_565 = l_reg_ts1755007860405;
            assign inj_out_data_pull0_1755007860405_693 = ~l_reg_ts1755007860405;
            // END: module_with_unconnected_drive_ts1755007860405

        always_comb begin
            l_reg_ts1755007860405 = 1;
            inj_wide_reg_1755007860405_619 = {clk, reset};
        end
        assign inj_o_sum_1755007860405_157 = clk + reset;
        // END: mod_lint_target_ts1755007860405

        // BEGIN: module_struct_ts1755007860404
        typedef struct packed {
            logic [3:0] part1_ts1755007860404;
            logic [7:0] part2_ts1755007860404;
            logic [3:0] part3_ts1755007860404;
        } my_packed_struct_t;
        my_packed_struct_t unpacked_data;
        assign unpacked_data = inj_i_packed_data_1755007860404_92;
        always @* begin
            inj_o_member_sum_1755007860404_445 = unpacked_data.part1_ts1755007860404 + unpacked_data.part2_ts1755007860404 + unpacked_data.part3_ts1755007860404;
        end
        // END: module_struct_ts1755007860404

        // BEGIN: simple_assign_ts1755007860404
        assign inj_out_1755007860404_571 = temp_data_ts1755007860403;
        // END: simple_assign_ts1755007860404

        // BEGIN: ModuleWithInterface_ts1755007860404
        MyInterface my_if (clk);
        assign my_if.req = 1'b1;
        assign inj_valid_out_1755007860404_13 = my_if.valid;
        // END: ModuleWithInterface_ts1755007860404

    always_comb begin
        if (inj_select_signal_1755007860403_906) begin
            temp_data_ts1755007860403 = inj_data_in_1755007860403_19 + 1;
        end else begin
            temp_data_ts1755007860403 = inj_data_in_1755007860403_19 - 1;
        end
        inj_data_out_1755007860403_824 = temp_data_ts1755007860403;
    end
    // END: SimpleLogicTest_ts1755007860403

    always @(inj_sel_1755007860403_523 or inj_data0_1755007860403_427 or inj_data1_1755007860403_904) begin
        if (inj_sel_1755007860403_523) begin
            inj_data_out_1755007860403_600 = inj_data1_1755007860403_904;
        end else begin
            inj_data_out_1755007860403_600 = inj_data0_1755007860403_427;
        end
    end
    // END: CombinationalLogicExplicit_ts1755007860403

    param_local_port param_local_port_inst_1755007860403_5463 (
        .i_reset(reset),
        .o_sum(inj_o_sum_1755007860403_940)
    );
    always_comb inj_y_1755007860403_281 = ~inj_a_1755007860403_653;
    // END: AlwaysCombInvert_ts1755007860403
endmodule

