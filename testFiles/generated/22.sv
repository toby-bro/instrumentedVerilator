interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module module_case_write (
    input logic [7:0] data_case_a,
    input logic [7:0] data_case_b,
    input logic [1:0] select_case,
    output logic case_output_ready
);
    my_if case_vif_inst();
    always_comb begin
        case (select_case)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = data_case_a;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = data_case_b;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        case_output_ready = case_vif_inst.ready;
    end
endmodule

module part_select_ops (
    input wire [31:0] wide_in,
    output wire [7:0] lower_byte_out,
    output wire [7:0] upper_byte_out
);
    wire [31:0] processed_wide;
    assign processed_wide = wide_in * 2;
    assign upper_byte_out = processed_wide[31:24];
    assign lower_byte_out = processed_wide[7:0];
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_case_a_1755004210454_9,
    input logic [7:0] inj_data_case_b_1755004210454_743,
    input bit inj_enable_in_1755004210458_535,
    input logic inj_in_a_1755004210454_514,
    input int inj_input_int_1755004210454_255,
    input logic [1:0] inj_select_case_1755004210454_424,
    input wire [31:0] inj_wide_in_1755004210459_433,
    input wire reset,
    output logic inj_case_output_ready_1755004210454_621,
    output wire [7:0] inj_lower_byte_out_1755004210459_675,
    output logic inj_o_done_1755004210456_646,
    output bit inj_out_1755004210458_698,
    output logic inj_out_b_1755004210454_200,
    output logic [7:0] inj_out_val_c_1755004210456_267,
    output int inj_output_int_1755004210454_890,
    output logic inj_q_1755004210455_667,
    output logic inj_unused_out_1755004210455_880,
    output wire [7:0] inj_upper_byte_out_1755004210459_820
);
    // BEGIN: func_macro_args_ts1755004210454
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var_ts1755004210454;
        // BEGIN: LintUnusedSignal_ts1755004210454
        logic unused_w_ts1755004210454; 
            // BEGIN: split_seq_dependency_ts1755004210456
            logic [7:0] mid_val_c_ts1755004210456;
                // BEGIN: mod_basic_ts1755004210457
                logic r_state_ts1755004210457;
                    part_select_ops part_select_ops_inst_1755004210459_3210 (
                        .upper_byte_out(inj_upper_byte_out_1755004210459_820),
                        .wide_in(inj_wide_in_1755004210459_433),
                        .lower_byte_out(inj_lower_byte_out_1755004210459_675)
                    );
                    // BEGIN: mod_default_disable_ts1755004210458
                    assign inj_out_1755004210458_698 = inj_enable_in_1755004210458_535;
                    // END: mod_default_disable_ts1755004210458

                parameter int PARAM_BASIC = 42;
                always_ff @(posedge clk) begin
                    r_state_ts1755004210457 <= ~r_state_ts1755004210457;
                end
                always_comb begin
                    inj_o_done_1755004210456_646 = r_state_ts1755004210457;
                end
                // END: mod_basic_ts1755004210457

            always @(posedge clk) begin
                mid_val_c_ts1755004210456 <= inj_data_case_a_1755004210454_9 + 1;
                inj_out_val_c_1755004210456_267 <= mid_val_c_ts1755004210456 * 2;
            end
            // END: split_seq_dependency_ts1755004210456

            // BEGIN: mod_seq_reg_ts1755004210455
            always_ff @(posedge clk) begin
                inj_q_1755004210455_667 <= inj_in_a_1755004210454_514;
            end
            // END: mod_seq_reg_ts1755004210455

            // BEGIN: mod_unused_ports_ts1755004210455
            assign inj_unused_out_1755004210455_880 = clk;
            // END: mod_unused_ports_ts1755004210455

            module_case_write module_case_write_inst_1755004210454_5661 (
                .data_case_b(inj_data_case_b_1755004210454_743),
                .select_case(inj_select_case_1755004210454_424),
                .case_output_ready(inj_case_output_ready_1755004210454_621),
                .data_case_a(inj_data_case_a_1755004210454_9)
            );
        assign inj_out_b_1755004210454_200 = inj_in_a_1755004210454_514;
        // END: LintUnusedSignal_ts1755004210454

    always_comb begin
        p2_sub_var_ts1755004210454 = `SUBTRACT(50, inj_input_int_1755004210454_255);
    end
    assign inj_output_int_1755004210454_890 = P1_ADD + p2_sub_var_ts1755004210454;
    // END: func_macro_args_ts1755004210454
endmodule

