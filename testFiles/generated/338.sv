interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModMultipleAlways (
    input logic clk_a,
    input logic clk_b,
    input logic din_a,
    input logic din_b,
    input logic rst_n,
    output logic dout_a,
    output logic dout_b
);
    always @(posedge clk_a or negedge rst_n) begin 
    if (!rst_n) begin 
        dout_a <= 1'b0;
    end else begin
        dout_a <= din_a; 
    end
    end
    always @(posedge clk_b) begin 
    dout_b <= din_b; 
    end
endmodule

module ModVectorAdd (
    input logic [7:0] in_v,
    output logic [7:0] out_v
);
    assign out_v = in_v + 8'h01;
endmodule

module SequentialLogic (
    input logic clk,
    input logic [7:0] data_in,
    input logic rst,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            internal_reg <= 8'h00;
        end else begin
            internal_reg <= data_in;
        end
    end
    assign data_out = internal_reg;
endmodule

module mod_basic (
    input wire i_clk,
    output logic o_done
);
    logic r_state;
    parameter int PARAM_BASIC = 42;
    always_ff @(posedge i_clk) begin
        r_state <= ~r_state;
    end
    always_comb begin
        o_done = r_state;
    end
endmodule

module module_task_args (
    input logic [7:0] arg_in_task,
    input logic [7:0] data_a_init_task,
    input logic start_task,
    output logic [7:0] data_a_out_task,
    output logic [7:0] data_b_out_task
);
    logic [7:0] data_a ;
    logic [7:0] data_b ;
    task automatic modify_vars;
        input logic [7:0] task_arg;
        logic [7:0] task_local ;
        begin
            task_local = task_arg;
            data_a = task_local + 8'd1;
            data_b = task_arg - 8'd1;
        end
    endtask
    always_comb begin
        if (start_task) begin
            data_a = data_a_init_task;
            data_b = 8'hFF;
            modify_vars(arg_in_task);
        end else begin
            data_a = 8'h00;
            data_b = 8'h00;
        end
    end
    always_comb begin
        data_a_out_task = data_a + 8'd2;
        data_b_out_task = data_b;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007867685_330,
    input logic [7:0] inj_data_a_init_task_1755007867685_368,
    input logic [3:0] inj_i_control_1755007867694_889,
    input logic inj_in_a_1755007867688_423,
    input int inj_in_val_1755007867690_808,
    input logic inj_keyword_in_1755007867685_722,
    input logic [1:0] inj_select_case_1755007867686_623,
    input wire reset,
    output logic inj_case_output_ready_1755007867686_745,
    output logic [7:0] inj_data_a_out_task_1755007867685_830,
    output logic [7:0] inj_data_a_out_task_1755007867704_412,
    output logic [7:0] inj_data_b_out_task_1755007867685_931,
    output logic [7:0] inj_data_b_out_task_1755007867704_775,
    output logic [7:0] inj_data_out_1755007867691_994,
    output logic inj_dout_a_1755007867696_208,
    output logic inj_dout_b_1755007867696_86,
    output logic inj_keyword_out_1755007867685_211,
    output logic inj_o_done_1755007867708_993,
    output logic [7:0] inj_o_result_1755007867694_883,
    output logic inj_o_status_1755007867694_215,
    output logic inj_out_a_1755007867699_656,
    output logic inj_out_c_1755007867688_962,
    output logic [7:0] inj_out_diff_m2_1755007867706_812,
    output reg inj_out_res_1755007867698_399,
    output logic [7:0] inj_out_v_1755007867695_432,
    output int inj_out_val_1755007867690_215,
    output int inj_out_val_1755007867701_626,
    output int inj_out_val_1755007867703_755,
    output logic [7:0] inj_var_out_m2_1755007867706_892
);
    // BEGIN: keyword_import_export_ts1755007867685
    // BEGIN: module_task_args_ts1755007867686
    logic [7:0] data_a_ts1755007867685 ;
    logic [7:0] data_b_ts1755007867685 ;
        // BEGIN: basic_assign_if_ts1755007867688
        logic intermediate_wire_ts1755007867688;
            // BEGIN: mod_name_conflict_ts1755007867699
            logic conflict_var_ts1755007867699;
                // BEGIN: expr_postsub_comb_ts1755007867706
                logic [7:0] var_m2_ts1755007867706;
                    mod_basic mod_basic_inst_1755007867708_4293 (
                        .o_done(inj_o_done_1755007867708_993),
                        .i_clk(clk)
                    );
                always_comb begin
                    var_m2_ts1755007867706 = inj_arg_in_task_1755007867685_330;
                    inj_out_diff_m2_1755007867706_812 = (var_m2_ts1755007867706--) - inj_data_a_init_task_1755007867685_368;
                    inj_var_out_m2_1755007867706_892 = var_m2_ts1755007867706;
                end
                // END: expr_postsub_comb_ts1755007867706

                module_task_args module_task_args_inst_1755007867704_1305 (
                    .data_b_out_task(inj_data_b_out_task_1755007867704_775),
                    .arg_in_task(inj_arg_in_task_1755007867685_330),
                    .data_a_init_task(data_a_ts1755007867685),
                    .start_task(intermediate_wire_ts1755007867688),
                    .data_a_out_task(inj_data_a_out_task_1755007867704_412)
                );
                // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007867703
                assign inj_out_val_1755007867703_755 = inj_in_val_1755007867690_808;
                // END: undeclared_but_found_pkg_diag_mod_ts1755007867703

                recursive_param_diag_mod recursive_param_diag_mod_inst_1755007867701_2826 (
                    .dummy_in(inj_in_val_1755007867690_808),
                    .out_val(inj_out_val_1755007867701_626)
                );
            parameter int conflict_param = 1;
            assign inj_out_a_1755007867699_656 = intermediate_wire_ts1755007867688;
            // END: mod_name_conflict_ts1755007867699

            // BEGIN: case_empty_statement_ts1755007867698
            always_comb begin
                inj_out_res_1755007867698_399 = 1'b0;
                case (inj_select_case_1755007867686_623)
                    2'b00: inj_out_res_1755007867698_399 = 1'b1;
                    2'b01: ;
                    2'b10: inj_out_res_1755007867698_399 = 1'b0;
                    default: inj_out_res_1755007867698_399 = 1'b1;
                endcase
            end
            // END: case_empty_statement_ts1755007867698

            ModMultipleAlways ModMultipleAlways_inst_1755007867696_9788 (
                .clk_a(clk),
                .clk_b(clk),
                .din_a(intermediate_wire_ts1755007867688),
                .din_b(inj_in_a_1755007867688_423),
                .rst_n(reset),
                .dout_a(inj_dout_a_1755007867696_208),
                .dout_b(inj_dout_b_1755007867696_86)
            );
            ModVectorAdd ModVectorAdd_inst_1755007867695_7089 (
                .in_v(inj_data_a_init_task_1755007867685_368),
                .out_v(inj_out_v_1755007867695_432)
            );
            // BEGIN: bind_directive_top_ts1755007867694
            target_module_for_bind target_inst(
                .i_target_clk   (clk),
                .i_target_data  (inj_arg_in_task_1755007867685_330),
                .o_target_result(inj_o_result_1755007867694_883)
            );
            module_to_bind bind_inst(
                .i_bind_clk     (clk),
                .i_bind_control (inj_i_control_1755007867694_889),
                .o_bind_status  (inj_o_status_1755007867694_215)
            );
            // END: bind_directive_top_ts1755007867694

            SequentialLogic SequentialLogic_inst_1755007867691_8872 (
                .clk(clk),
                .data_in(inj_arg_in_task_1755007867685_330),
                .rst(reset),
                .data_out(inj_data_out_1755007867691_994)
            );
            // BEGIN: local_not_allowed_diag_mod_ts1755007867690
            assign inj_out_val_1755007867690_215 = inj_in_val_1755007867690_808;
            // END: local_not_allowed_diag_mod_ts1755007867690

        assign intermediate_wire_ts1755007867688 = inj_in_a_1755007867688_423 & inj_keyword_in_1755007867685_722;
        always_comb begin
            if (intermediate_wire_ts1755007867688) begin
                inj_out_c_1755007867688_962 = 1'b1;
            end else begin
                inj_out_c_1755007867688_962 = 1'b0;
            end
        end
        // END: basic_assign_if_ts1755007867688

        // BEGIN: module_case_write_ts1755007867687
        my_if case_vif_inst();
        always_comb begin
            case (inj_select_case_1755007867686_623)
                2'b00: begin
                    case_vif_inst.data = 8'hAA;
                    case_vif_inst.valid = 1'b1;
                    case_vif_inst.ready = 1'b0;
                end
                2'b01: begin
                    case_vif_inst.data = data_b_ts1755007867685;
                    case_vif_inst.valid = 1'b0;
                    case_vif_inst.ready = 1'b1;
                end
                2'b10: begin
                    case_vif_inst.data = inj_arg_in_task_1755007867685_330;
                    case_vif_inst.valid = 1'b1;
                    case_vif_inst.ready = 1'b1;
                end
                default: begin
                    case_vif_inst.data = 8'hFF;
                    case_vif_inst.valid = 1'b0;
                    case_vif_inst.ready = 1'b0;
                end
            endcase
            inj_case_output_ready_1755007867686_745 = case_vif_inst.ready;
        end
        // END: module_case_write_ts1755007867687

    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007867685;
        logic [7:0] task_local_ts1755007867685 ;
        begin
            task_local_ts1755007867685 = task_arg_ts1755007867685;
            data_a_ts1755007867685 = task_local_ts1755007867685 + 8'd1;
            data_b_ts1755007867685 = task_arg_ts1755007867685 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_keyword_in_1755007867685_722) begin
            data_a_ts1755007867685 = inj_data_a_init_task_1755007867685_368;
            data_b_ts1755007867685 = 8'hFF;
            modify_vars(inj_arg_in_task_1755007867685_330);
        end else begin
            data_a_ts1755007867685 = 8'h00;
            data_b_ts1755007867685 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007867685_830 = data_a_ts1755007867685 + 8'd2;
        inj_data_b_out_task_1755007867685_931 = data_b_ts1755007867685;
    end
    // END: module_task_args_ts1755007867686

    assign inj_keyword_out_1755007867685_211 = inj_keyword_in_1755007867685_722;
    // END: keyword_import_export_ts1755007867685
endmodule

