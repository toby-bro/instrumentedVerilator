module Module_BasicSyntax (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic out_cmp,
    output logic [7:0] out_ops
);
    logic [7:0] temp;
    always_comb begin
        temp = in_a + in_b;
    end
    assign out_ops = (in_a & in_b) | (in_a ^ in_b);
    assign out_cmp = (in_a == in_b);
endmodule

module child_empty_ports (
    p1,
    p2
);
    input logic p1;
    output logic p2;
    assign p2 = p1;
endmodule

module snippet (
    input wire clk,
    input logic inj_i_1755007773902_120,
    input logic [7:0] inj_in_a_1755007773901_925,
    input logic [7:0] inj_in_val_1755007773900_216,
    input logic [31:0] inj_input_pa_1755007773904_803,
    input logic [3:0] inj_start_val_1755007773903_775,
    input wire reset,
    output logic [7:0] inj_final_val_1755007773903_591,
    output logic inj_o_1755007773902_613,
    output logic [3:0] inj_out_1755007773901_260,
    output logic inj_out_cmp_1755007773901_551,
    output logic inj_out_e_1755007773906_490,
    output logic [7:0] inj_out_ops_1755007773901_576,
    output logic [7:0] inj_out_val_1755007773900_519,
    output logic [7:0] inj_output_pa_1755007773904_563,
    output logic [7:0] inj_output_pa_element1_1755007773904_549,
    output logic inj_p2_1755007773903_3,
    output logic inj_q_out_1755007773902_91
);
    // BEGIN: generic_class_scope_diag_mod_ts1755007773900
    // BEGIN: mismatched_width_unhandled_ts1755007773901
    // BEGIN: child_module_v2_config_dummy_ts1755007773902
    // BEGIN: LogicDependencyChain_ts1755007773902
    logic q1_ts1755007773902, q2_ts1755007773902;
        // BEGIN: loop_with_internal_assign_ts1755007773903
        logic [7:0] current_val_ts1755007773903;
            // BEGIN: LintCombBlockAssign_ts1755007773906
            always_comb begin
                inj_out_e_1755007773906_490 = q2_ts1755007773902 & inj_i_1755007773902_120;
            end
            // END: LintCombBlockAssign_ts1755007773906

            // BEGIN: module_packed_array_ts1755007773905
            logic [7:0] my_packed_array[0:3] ;
            always_comb begin
                if (q1_ts1755007773902) begin
                    my_packed_array[0] = inj_input_pa_1755007773904_803[7:0];
                    my_packed_array[1] = inj_input_pa_1755007773904_803[15:8];
                    my_packed_array[2] = inj_input_pa_1755007773904_803[23:16];
                    my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
                end else begin
                    my_packed_array[0] = 8'h0;
                    my_packed_array[1] = 8'h0;
                    my_packed_array[2] = 8'h0;
                    my_packed_array[3] = 8'h0;
                end
                my_packed_array[0][3:0] = inj_start_val_1755007773903_775;
            end
            assign inj_output_pa_1755007773904_563 = my_packed_array[3];
            assign inj_output_pa_element1_1755007773904_549 = my_packed_array[1];
            // END: module_packed_array_ts1755007773905

            child_empty_ports child_empty_ports_inst_1755007773903_6230 (
                .p1(inj_i_1755007773902_120),
                .p2(inj_p2_1755007773903_3)
            );
        always_comb begin
            current_val_ts1755007773903 = inj_start_val_1755007773903_775;
            for (int k = 0; k < 3; k = k + 1) begin
                current_val_ts1755007773903 = current_val_ts1755007773903 + 1;
            end
            inj_final_val_1755007773903_591 = current_val_ts1755007773903;
        end
        // END: loop_with_internal_assign_ts1755007773903

    always @(posedge clk) begin
        q1_ts1755007773902 <= inj_i_1755007773902_120;
    end
    always @(q1_ts1755007773902) begin
        q2_ts1755007773902 = ~q1_ts1755007773902;
    end
    assign inj_q_out_1755007773902_91 = q2_ts1755007773902;
    // END: LogicDependencyChain_ts1755007773902

    assign inj_o_1755007773902_613 = inj_i_1755007773902_120 | inj_i_1755007773902_120; 
    // END: child_module_v2_config_dummy_ts1755007773902

    Module_BasicSyntax Module_BasicSyntax_inst_1755007773901_6223 (
        .in_a(inj_in_a_1755007773901_925),
        .in_b(inj_in_val_1755007773900_216),
        .out_cmp(inj_out_cmp_1755007773901_551),
        .out_ops(inj_out_ops_1755007773901_576)
    );
    assign inj_out_1755007773901_260 = inj_in_val_1755007773900_216;
    // END: mismatched_width_unhandled_ts1755007773901

    assign inj_out_val_1755007773900_519 = inj_in_val_1755007773900_216;
    // END: generic_class_scope_diag_mod_ts1755007773900
endmodule

