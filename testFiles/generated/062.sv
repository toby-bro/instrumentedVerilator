interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module CombinationalLogicExplicit (
    input logic [15:0] data0,
    input logic [15:0] data1,
    input logic sel,
    output logic [15:0] data_out
);
    always @(sel or data0 or data1) begin
        if (sel) begin
            data_out = data1;
        end else begin
            data_out = data0;
        end
    end
endmodule

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

module ModuleHierarchy_High #(
    parameter int SEL_PARAM = 6
) (
    input logic [3:0] data_in,
    input int sel_in,
    output logic [7:0] data_out
);
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (sel_in),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule

module Module_MacroTokens (
    input logic tok_in,
    output logic tok_out
);
    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = tok_in;
        tok_out         = `PASTE(my,_var);
    end
endmodule

module case_basic (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule

module case_selector (
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [1:0] sel_in,
    output logic [3:0] data_out_case
);
    always_comb begin
        case (sel_in)
            2'b00: data_out_case = data0; 
            2'b01: data_out_case = data1; 
            2'b10: data_out_case = data2; 
            default: data_out_case = data3; 
        endcase
    end
endmodule

module casez_xz_alt (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1?z: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module cast_select_demo (
    input logic [7:0] in_data,
    output logic [1:0] out_bits
);
    logic [7:0] internal;
    always_comb begin
        internal = in_data;
        out_bits = internal[3 -: 2];
    end
endmodule

module member_access_packed_union (
    input logic [31:0] in_val,
    input bit select_a,
    output logic [31:0] out_val
);
    typedef union packed {
        logic [31:0] a; 
        logic [31:0] b; 
    } my_packed_union;
    my_packed_union union_var;
    always_comb begin
        if (select_a)
            union_var.a = in_val;
        else
            union_var.b = in_val[31:0];
        out_val = union_var.a;
    end
endmodule

module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule

module module_assign_blocking (
    input logic [7:0] in_data,
    output logic out_valid_status
);
    my_if vif_inst();
    always_comb begin
        vif_inst.data = in_data;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        out_valid_status = vif_inst.valid;
    end
endmodule

module rand_case_mod (
    input logic [2:0] selector,
    output logic [3:0] result_out
);
    always_comb begin
        case (selector)
            0: result_out = 4'h0;
            1: result_out = 4'h1;
            2: result_out = 4'hA;
            default: result_out = 4'hF;
        endcase
    end
endmodule

module split_multiple_in_branch (
    input logic clk_j,
    input logic condition_j,
    input logic [7:0] in_a_j,
    input logic [7:0] in_b_j,
    output logic [7:0] out_x_j,
    output logic [7:0] out_y_j
);
    always @(posedge clk_j) begin
        if (condition_j) begin
            out_x_j <= in_a_j * 3;
            out_y_j <= in_b_j + 1;
        end else begin
            out_x_j <= in_a_j;
            out_y_j <= in_b_j;
        end
    end
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input logic [3:0] inj_data0_1755007772445_178,
    input logic [7:0] inj_data1_1755007772443_141,
    input logic [3:0] inj_data1_1755007772445_326,
    input logic [15:0] inj_data1_1755007772524_755,
    input logic [7:0] inj_data2_1755007772443_590,
    input logic [3:0] inj_data2_1755007772445_43,
    input logic [7:0] inj_data3_1755007772443_878,
    input logic [3:0] inj_data3_1755007772445_562,
    input logic inj_data_value_1755007772443_283,
    input int inj_dummy_in_1755007772448_115,
    input logic [7:0] inj_in_data_1755007772443_748,
    input logic [31:0] inj_in_val_1755007772444_594,
    input logic [2:0] inj_in_val_1755007772451_196,
    input logic inj_level1_en_1755007772443_403,
    input logic inj_level2_en_1755007772443_380,
    input logic [15:0] inj_packed_in_1755007772467_492,
    input logic [1:0] inj_sel_code_1755007772443_607,
    input bit inj_select_a_1755007772444_213,
    input wire reset,
    output bit inj_d_out_1755007772496_314,
    output logic [7:0] inj_data_out_1755007772454_934,
    output logic inj_data_out_1755007772457_644,
    output logic [3:0] inj_data_out_1755007772478_967,
    output int inj_data_out_1755007772481_813,
    output reg inj_data_out_1755007772485_739,
    output logic [15:0] inj_data_out_1755007772524_604,
    output logic [3:0] inj_data_out_case_1755007772445_916,
    output logic [7:0] inj_dout_1755007772513_7,
    output logic [7:0] inj_field2_o_1755007772467_635,
    output logic [4:0] inj_internal_out_1755007772529_97,
    output logic [7:0] inj_o1_r_1755007772475_722,
    output logic [7:0] inj_o2_r_1755007772475_400,
    output logic [7:0] inj_o3_r_1755007772475_728,
    output logic [7:0] inj_o_array_var_elem_1755007772472_139,
    output logic inj_o_sel_var_bit_1755007772472_569,
    output bit inj_out_1755007772465_954,
    output logic inj_out_a_1755007772508_310,
    output int inj_out_b_1755007772508_132,
    output logic [1:0] inj_out_bits_1755007772443_132,
    output logic inj_out_e_1755007772470_620,
    output logic inj_out_m9_1755007772499_705,
    output logic [7:0] inj_out_reg_t_1755007772492_712,
    output reg inj_out_res_1755007772451_356,
    output reg inj_out_res_1755007772452_940,
    output logic [31:0] inj_out_val_1755007772444_291,
    output int inj_out_val_1755007772448_341,
    output int inj_out_val_1755007772450_879,
    output logic inj_out_valid_status_1755007772463_596,
    output logic [7:0] inj_out_x_j_1755007772459_86,
    output logic [7:0] inj_out_y_j_1755007772459_140,
    output logic [7:0] inj_output_pa_1755007772460_69,
    output logic [7:0] inj_output_pa_element1_1755007772460_736,
    output logic inj_p2_1755007772446_35,
    output logic [3:0] inj_result_1755007772447_26,
    output logic inj_result_out_1755007772443_52,
    output logic [3:0] inj_result_out_1755007772489_779,
    output logic [3:0] inj_result_out_1755007772504_405,
    output logic [7:0] inj_selected_data_1755007772443_111,
    output logic inj_tok_out_1755007772519_751
);
    // BEGIN: IfElseIfChain_ts1755007772443
    // BEGIN: nested_blocks_ts1755007772444
    // BEGIN: child_empty_ports_ts1755007772446
    input logic inj_level2_en_1755007772443_380_ts1755007772446;
    output logic inj_p2_1755007772446_35_ts1755007772446;
        // BEGIN: HandleOutOfBoundsRead_ts1755007772472
        parameter ARR_SIZE = 4;
        logic [7:0] my_array_ts1755007772472 [0:ARR_SIZE-1];
            // BEGIN: split_complex_blocking_ts1755007772475
            logic [7:0] t1_r_ts1755007772475, t2_r_ts1755007772475;
                // BEGIN: sequential_logic_ts1755007772478
                ;
                logic [3:0] internal_reg_ts1755007772478;
                    // BEGIN: unsupported_logand_expr_ts1755007772500
                    logic [7:0] var_m9_ts1755007772500;
                        // BEGIN: ModuleBasic_ts1755007772508
                        parameter int P1  = 10;
                        localparam int LP1 = 20;
                        logic c_ts1755007772508;
                        int   d_ts1755007772508;
                        always_comb begin
                            logic temp_v_ts1755007772508;
                                // BEGIN: case_full_parallel_mod_ts1755007772529
                                always @* begin
                                    (* full, parallel *)
                                    case (inj_sel_code_1755007772443_607)
                                        2'b00: inj_internal_out_1755007772529_97 = 1;
                                        2'b01: inj_internal_out_1755007772529_97 = 2;
                                        2'b10: inj_internal_out_1755007772529_97 = 3;
                                        default: inj_internal_out_1755007772529_97 = 4;
                                    endcase
                                end
                                // END: case_full_parallel_mod_ts1755007772529

                                CombinationalLogicExplicit CombinationalLogicExplicit_inst_1755007772524_9437 (
                                    .data_out(inj_data_out_1755007772524_604),
                                    .data0(inj_packed_in_1755007772467_492),
                                    .data1(inj_data1_1755007772524_755),
                                    .sel(inj_level1_en_1755007772443_403)
                                );
                                Module_MacroTokens Module_MacroTokens_inst_1755007772519_5868 (
                                    .tok_in(inj_level2_en_1755007772443_380),
                                    .tok_out(inj_tok_out_1755007772519_751)
                                );
                                // BEGIN: Parameterized_ts1755007772513
                                assign inj_dout_1755007772513_7 = inj_data2_1755007772443_590;
                                // END: Parameterized_ts1755007772513

                            temp_v_ts1755007772508 = d_ts1755007772508;
                            c_ts1755007772508      = temp_v_ts1755007772508;
                        end
                        assign inj_out_a_1755007772508_310 = inj_level2_en_1755007772443_380;
                        assign d_ts1755007772508     = inj_dummy_in_1755007772448_115;
                        assign inj_out_b_1755007772508_132 = d_ts1755007772508 + P1 + LP1;
                        // END: ModuleBasic_ts1755007772508

                        rand_case_mod rand_case_mod_inst_1755007772504_4860 (
                            .selector(inj_in_val_1755007772451_196),
                            .result_out(inj_result_out_1755007772504_405)
                        );
                    always_comb begin
                        var_m9_ts1755007772500 = inj_data3_1755007772443_878;
                        if ((var_m9_ts1755007772500 > 10) && (t1_r_ts1755007772475 < 5)) begin
                            inj_out_m9_1755007772499_705 = 1;
                        end else begin
                            inj_out_m9_1755007772499_705 = 0;
                        end
                        var_m9_ts1755007772500++;
                    end
                    // END: unsupported_logand_expr_ts1755007772500

                    // BEGIN: DummyBindTarget_ts1755007772496
                    assign inj_d_out_1755007772496_314 = inj_select_a_1755007772444_213;
                    BindSimpleModule u_bind (.in(inj_select_a_1755007772444_213), .out());
                    // END: DummyBindTarget_ts1755007772496

                    // BEGIN: split_if_empty_branches_ts1755007772492
                    always @(posedge clk) begin
                        if (inj_level2_en_1755007772443_380) begin
                        end else begin
                        end
                    end
                    // END: split_if_empty_branches_ts1755007772492

                    rand_case_mod rand_case_mod_inst_1755007772489_3547 (
                        .selector(inj_in_val_1755007772451_196),
                        .result_out(inj_result_out_1755007772489_779)
                    );
                    // BEGIN: mod_event_posedge_ts1755007772485
                    always @(posedge clk) begin
                        inj_data_out_1755007772485_739 <= reset;
                    end
                    // END: mod_event_posedge_ts1755007772485

                    mod_named_begin mod_named_begin_inst_1755007772481_2795 (
                        .data_out(inj_data_out_1755007772481_813),
                        .data_in(inj_dummy_in_1755007772448_115)
                    );
                always_ff @(posedge clk or negedge reset) begin
                    if (!reset) begin
                        internal_reg_ts1755007772478 <= 4'h0;
                    end else begin
                        internal_reg_ts1755007772478 <= inj_data3_1755007772445_562;
                    end
                end
                assign inj_data_out_1755007772478_967 = internal_reg_ts1755007772478;
                // END: sequential_logic_ts1755007772478

            always @(*) begin
                t1_r_ts1755007772475 = inj_data2_1755007772443_590 + inj_data3_1755007772443_878;
                inj_o1_r_1755007772475_722 = t1_r_ts1755007772475 - my_array_ts1755007772472;
                t2_r_ts1755007772475 = inj_data3_1755007772443_878 * my_array_ts1755007772472;
                inj_o2_r_1755007772475_400 = t1_r_ts1755007772475 + t2_r_ts1755007772475;
                inj_o3_r_1755007772475_728 = t2_r_ts1755007772475 / 2;
            end
            // END: split_complex_blocking_ts1755007772475

        assign my_array_ts1755007772472[0] = 8'd10;
        assign my_array_ts1755007772472[1] = 8'd20;
        assign my_array_ts1755007772472[2] = 8'd30;
        assign my_array_ts1755007772472[3] = 8'd40;
        assign inj_o_sel_var_bit_1755007772472_569 = inj_in_data_1755007772443_748[inj_data3_1755007772445_562];
        assign inj_o_array_var_elem_1755007772472_139 = my_array_ts1755007772472[inj_data1_1755007772445_326];
        // END: HandleOutOfBoundsRead_ts1755007772472

        // BEGIN: LintCombBlockAssign_ts1755007772470
        always_comb begin
            inj_out_e_1755007772470_620 = inj_p2_1755007772446_35_ts1755007772446 & inj_level2_en_1755007772443_380_ts1755007772446;
        end
        // END: LintCombBlockAssign_ts1755007772470

        // BEGIN: typedef_struct_mod_ts1755007772468
        typedef struct packed {
            logic [7:0] field1_ts1755007772468;
            logic [7:0] field2_ts1755007772468;
        } my_packed_struct_t;
        my_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755007772467_492;
        end
        assign inj_field2_o_1755007772467_635 = my_struct_var.field2_ts1755007772468;
        // END: typedef_struct_mod_ts1755007772468

        // BEGIN: mod_default_disable_ts1755007772465
        assign inj_out_1755007772465_954 = inj_select_a_1755007772444_213;
        // END: mod_default_disable_ts1755007772465

        module_assign_blocking module_assign_blocking_inst_1755007772463_8911 (
            .in_data(inj_data2_1755007772443_590),
            .out_valid_status(inj_out_valid_status_1755007772463_596)
        );
        // BEGIN: module_packed_array_ts1755007772461
        logic [7:0] my_packed_array[0:3] ;
        always_comb begin
            if (inj_level2_en_1755007772443_380_ts1755007772446) begin
                my_packed_array[0] = inj_in_val_1755007772444_594[7:0];
                my_packed_array[1] = inj_in_val_1755007772444_594[15:8];
                my_packed_array[2] = inj_in_val_1755007772444_594[23:16];
                my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
            end else begin
                my_packed_array[0] = 8'h0;
                my_packed_array[1] = 8'h0;
                my_packed_array[2] = 8'h0;
                my_packed_array[3] = 8'h0;
            end
            my_packed_array[0][3:0] = inj_data1_1755007772445_326;
        end
        assign inj_output_pa_1755007772460_69 = my_packed_array[3];
        assign inj_output_pa_element1_1755007772460_736 = my_packed_array[1];
        // END: module_packed_array_ts1755007772461

        split_multiple_in_branch split_multiple_in_branch_inst_1755007772459_5182 (
            .clk_j(clk),
            .condition_j(inj_p2_1755007772446_35_ts1755007772446),
            .in_a_j(inj_data1_1755007772443_141),
            .in_b_j(inj_data2_1755007772443_590),
            .out_x_j(inj_out_x_j_1755007772459_86),
            .out_y_j(inj_out_y_j_1755007772459_140)
        );
        // BEGIN: child_scalar_port_ts1755007772457
        assign inj_data_out_1755007772457_644 = inj_level2_en_1755007772443_380_ts1755007772446;
        // END: child_scalar_port_ts1755007772457

        ModuleHierarchy_High ModuleHierarchy_High_inst_1755007772454_6381 (
            .data_in(inj_data0_1755007772445_178),
            .sel_in(inj_dummy_in_1755007772448_115),
            .data_out(inj_data_out_1755007772454_934)
        );
        case_basic case_basic_inst_1755007772452_3979 (
            .in_val(inj_sel_code_1755007772443_607),
            .out_res(inj_out_res_1755007772452_940)
        );
        casez_xz_alt casez_xz_alt_inst_1755007772451_2764 (
            .in_val(inj_in_val_1755007772451_196),
            .out_res(inj_out_res_1755007772451_356)
        );
        // BEGIN: simple_undeclared_mod_ts1755007772450
        assign inj_out_val_1755007772450_879 = inj_dummy_in_1755007772448_115;
        // END: simple_undeclared_mod_ts1755007772450

        // BEGIN: recursive_param_diag_mod_ts1755007772448
        assign inj_out_val_1755007772448_341 = inj_dummy_in_1755007772448_115;
        // END: recursive_param_diag_mod_ts1755007772448

        // BEGIN: CombinationalLogic_ts1755007772447
        always_comb begin
            if (inj_level2_en_1755007772443_380_ts1755007772446) begin
                inj_result_1755007772447_26 = inj_data0_1755007772445_178 + inj_data2_1755007772445_43;
            end else begin
                inj_result_1755007772447_26 = 4'h0;
            end
        end
        // END: CombinationalLogic_ts1755007772447

    assign inj_p2_1755007772446_35_ts1755007772446 = inj_level2_en_1755007772443_380_ts1755007772446;
    // END: child_empty_ports_ts1755007772446

    case_selector case_selector_inst_1755007772445_9759 (
        .data0(inj_data0_1755007772445_178),
        .data1(inj_data1_1755007772445_326),
        .data2(inj_data2_1755007772445_43),
        .data3(inj_data3_1755007772445_562),
        .sel_in(inj_sel_code_1755007772443_607),
        .data_out_case(inj_data_out_case_1755007772445_916)
    );
    member_access_packed_union member_access_packed_union_inst_1755007772444_4839 (
        .select_a(inj_select_a_1755007772444_213),
        .out_val(inj_out_val_1755007772444_291),
        .in_val(inj_in_val_1755007772444_594)
    );
    always_comb begin : main_block 
        inj_result_out_1755007772443_52 = 1'b0; 
        if (inj_level1_en_1755007772443_403) begin : inner_block1 
            if (inj_level2_en_1755007772443_380) begin : inner_block2 
                inj_result_out_1755007772443_52 = inj_data_value_1755007772443_283;
            end 
        end 
    end
    // END: nested_blocks_ts1755007772444

    always_comb begin
        if (inj_sel_code_1755007772443_607 == 2'b00) begin
            inj_selected_data_1755007772443_111 = inj_in_data_1755007772443_748;
        end else if (inj_sel_code_1755007772443_607 == 2'b01) begin
            inj_selected_data_1755007772443_111 = inj_data1_1755007772443_141;
        end else if (inj_sel_code_1755007772443_607 == 2'b10) begin
            inj_selected_data_1755007772443_111 = inj_data2_1755007772443_590;
        end else begin
            inj_selected_data_1755007772443_111 = inj_data3_1755007772443_878;
        end
    end
    // END: IfElseIfChain_ts1755007772443

    cast_select_demo cast_select_demo_inst_1755007772443_3906 (
        .in_data(inj_in_data_1755007772443_748),
        .out_bits(inj_out_bits_1755007772443_132)
    );
endmodule

