module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module expr_preadd_comb (
    input logic [7:0] add_val_m1,
    input logic [7:0] in_val_m1,
    output logic [7:0] out_sum_m1,
    output logic [7:0] var_out_m1
);
    logic [7:0] var_m1;
    always_comb begin
        var_m1 = in_val_m1;
        out_sum_m1 = (++var_m1) + add_val_m1;
        var_out_m1 = var_m1;
    end
endmodule

module snippet #(
    parameter int SEL_PARAM = 5
) (
    input wire clk,
    input logic [7:0] inj_add_val_m1_1755004208685_30,
    input bit inj_condition_m10_1755004208695_670,
    input wire [31:0] inj_data_in_1755004208680_336,
    input logic [3:0] inj_data_in_1755004208681_253,
    input wire [15:0] inj_i_packed_data_1755004208680_836,
    input logic inj_in1_1755004208681_199,
    input logic [7:0] inj_in_val_m1_1755004208685_547,
    input logic [3:0] inj_p_b_1755004208691_126,
    input int inj_sel_in_1755004208681_890,
    input wire reset,
    output logic [31:0] inj_data_out_1755004208680_475,
    output logic [7:0] inj_data_out_1755004208681_299,
    output logic inj_o_attr_out_1755004208683_86,
    output logic [7:0] inj_o_member_sum_1755004208680_322,
    output logic [31:0] inj_out1_1755004208681_611,
    output logic inj_out_data_pull0_1755004208689_457,
    output logic inj_out_data_pull1_1755004208689_905,
    output logic [7:0] inj_out_sum_m1_1755004208685_206,
    output int inj_out_val_1755004208687_100,
    output logic [7:0] inj_out_val_m10_1755004208695_858,
    output int inj_output_int_1755004208693_59,
    output logic inj_single_out_1755004208691_484,
    output logic [7:0] inj_var_out_m1_1755004208685_582
);
    // BEGIN: mod_part_select_ts1755004208680
    logic [31:0] temp_reg_ts1755004208680;
        // BEGIN: ModuleHierarchy_Low_ts1755004208682
        ModuleBasic m1 (
            .a     (1'b1),
            .b     (inj_sel_in_1755004208681_890),
            .out_a (),
            .out_b ( )
        );
        if (SEL_PARAM > 5) begin : gen_high
            int high_data_ts1755004208682;
            ModuleBasic m_high (
                .a     (1'b0),
                .b     (SEL_PARAM),
                .out_a (),
                .out_b (high_data_ts1755004208682)
            );
        end else begin : gen_low
            int low_data_ts1755004208682;
            ModuleBasic m_low (
                .a     (1'b0),
                .b     (SEL_PARAM),
                .out_a (),
                .out_b (low_data_ts1755004208682)
            );
        end
        for (genvar i = 0; i < 2; ++i) begin : gen_loop
            logic [1:0] sub_in_ts1755004208682;
            assign sub_in_ts1755004208682 = inj_data_in_1755004208681_253[i*2 +: 2];
            int temp_int_ts1755004208682;
                // BEGIN: func_macro_args_ts1755004208693
                `define ADD(a, b)       ((a) + (b))
                `define SUBTRACT(x, y)  ((x) - (y))
                localparam int P1_ADD = `ADD(10, 20);
                int p2_sub_var_ts1755004208693;
                    // BEGIN: unsupported_cond_expr_ts1755004208695
                    logic [7:0] var_m10_ts1755004208695;
                    always_comb begin
                        var_m10_ts1755004208695 = inj_in_val_m1_1755004208685_547;
                        inj_out_val_m10_1755004208695_858 = inj_condition_m10_1755004208695_670 ? var_m10_ts1755004208695 : var_m10_ts1755004208695;
                        var_m10_ts1755004208695++;
                    end
                    // END: unsupported_cond_expr_ts1755004208695

                always_comb begin
                    p2_sub_var_ts1755004208693 = `SUBTRACT(50, temp_int_ts1755004208682);
                end
                assign inj_output_int_1755004208693_59 = P1_ADD + p2_sub_var_ts1755004208693;
                // END: func_macro_args_ts1755004208693

                // BEGIN: multi_port_decl_module_ts1755004208691
                always_comb begin
                    inj_single_out_1755004208691_484 = inj_in1_1755004208681_199;
                end
                // END: multi_port_decl_module_ts1755004208691

                // BEGIN: module_with_unconnected_drive_ts1755004208689
                assign inj_out_data_pull1_1755004208689_905 = inj_in1_1755004208681_199;
                assign inj_out_data_pull0_1755004208689_457 = ~inj_in1_1755004208681_199;
                // END: module_with_unconnected_drive_ts1755004208689

                // BEGIN: ConditionalOps_ts1755004208687
                assign inj_out_val_1755004208687_100 = inj_in1_1755004208681_199 ? inj_sel_in_1755004208681_890 : temp_int_ts1755004208682;
                // END: ConditionalOps_ts1755004208687

                expr_preadd_comb expr_preadd_comb_inst_1755004208685_5613 (
                    .out_sum_m1(inj_out_sum_m1_1755004208685_206),
                    .var_out_m1(inj_var_out_m1_1755004208685_582),
                    .add_val_m1(inj_add_val_m1_1755004208685_30),
                    .in_val_m1(inj_in_val_m1_1755004208685_547)
                );
                // BEGIN: attributes_test_ts1755004208683
                (* synthesis_preserve *) logic internal_signal;
                always_comb begin : my_combinational_block
                    internal_signal = inj_in1_1755004208681_199 ? 1'b1 : 1'b0;
                    inj_o_attr_out_1755004208683_86      = internal_signal;
                end
                // END: attributes_test_ts1755004208683

            ModuleBasic m_inst (
                .a      (1'b0),
                .b      (int'(sub_in_ts1755004208682)),
                .out_a  (),
                .out_b  (temp_int_ts1755004208682)
            );
            assign inj_data_out_1755004208681_299[i*4 +: 4] = temp_int_ts1755004208682[3:0];
        end
        // END: ModuleHierarchy_Low_ts1755004208682

        // BEGIN: simple_macro_user_ts1755004208681
        `define SIMPLE_VALUE 32'd12345
        `define ANOTHER_SIMPLE (1 + 2)
        assign inj_out1_1755004208681_611 = inj_in1_1755004208681_199 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
        // END: simple_macro_user_ts1755004208681

        // BEGIN: module_struct_ts1755004208680
        typedef struct packed {
            logic [3:0] part1_ts1755004208680;
            logic [7:0] part2_ts1755004208680;
            logic [3:0] part3_ts1755004208680;
        } my_packed_struct_t;
        my_packed_struct_t unpacked_data;
        assign unpacked_data = inj_i_packed_data_1755004208680_836;
        always @* begin
            inj_o_member_sum_1755004208680_322 = unpacked_data.part1_ts1755004208680 + unpacked_data.part2_ts1755004208680 + unpacked_data.part3_ts1755004208680;
        end
        // END: module_struct_ts1755004208680

    always_comb begin
        temp_reg_ts1755004208680[7:0] = inj_data_in_1755004208680_336[7:0];
        temp_reg_ts1755004208680[15:8] = inj_data_in_1755004208680_336[23:16];
        temp_reg_ts1755004208680[31:16] = inj_data_in_1755004208680_336[15:0];
        temp_reg_ts1755004208680[0] = inj_data_in_1755004208680_336[31];
        temp_reg_ts1755004208680[8] = inj_data_in_1755004208680_336[0];
        inj_data_out_1755004208680_475 = temp_reg_ts1755004208680;
    end
    // END: mod_part_select_ts1755004208680
endmodule

