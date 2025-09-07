interface MyInterface (
    input logic clk
);
    logic req;
    logic valid;
    modport master (output req, input valid, input clk);
    modport slave (input req, output valid, input clk);
endinterface
interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModuleWithInterface (
    input logic clk_in,
    output logic valid_out
);
    MyInterface my_if (clk_in);
    assign my_if.req = 1'b1;
    assign valid_out = my_if.valid;
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

module mod_name_conflict (
    input logic in_a,
    output logic out_a
);
    logic conflict_var;
    parameter int conflict_param = 1;
    assign out_a = in_a;
endmodule

module module_task_write (
    input logic [7:0] in_task_data,
    input logic task_en,
    output logic task_output_valid
);
    my_if task_vif_inst();
    task automatic update_vif_signals(input logic en, input logic [7:0] data_val,
        output logic [7:0] vif_data, output logic vif_valid, output logic vif_ready);
        if (en) begin
            vif_data = data_val;
            vif_valid = 1'b1;
            vif_ready = 1'b0;
        end else begin
            vif_data = 8'h0;
            vif_valid = 1'b0;
            vif_ready = 1'b1;
        end
    endtask
    always_comb begin
        update_vif_signals(task_en, in_task_data, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        task_output_valid = task_vif_inst.valid;
    end
endmodule

module recursive_macro_dummy (
    input logic in_bit,
    output logic out_bit
);
    `define RECURSIVE_TEST `RECURSIVE_TEST
    assign out_bit = in_bit;
endmodule

module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_condition_p_1755007878145_613,
    input logic [7:0] inj_d1_w_1755007878147_154,
    input logic [7:0] inj_d2_w_1755007878147_856,
    input logic [3:0] inj_data0_1755007878146_473,
    input logic [3:0] inj_data1_1755007878146_259,
    input logic [3:0] inj_data2_1755007878146_67,
    input logic [3:0] inj_data3_1755007878146_54,
    input wire [3:0] inj_data_c_1755007878146_599,
    input logic inj_in_b_1755007878147_914,
    input logic [7:0] inj_in_true_o_1755007878146_651,
    input logic [7:0] inj_in_val_p_1755007878145_378,
    input logic [1:0] inj_sel_in_1755007878146_174,
    input wire [1:0] inj_selector_1755007878146_468,
    input wire reset,
    output logic [3:0] inj_data_out_case_1755007878146_672,
    output logic [7:0] inj_out1_a_1755007878145_289,
    output wire inj_out_1755007878149_301,
    output logic inj_out_a_1755007878148_894,
    output logic inj_out_bit_1755007878146_291,
    output logic inj_out_c_1755007878147_795,
    output logic [3:0] inj_out_case_case_1755007878146_397,
    output logic [3:0] inj_out_case_casex_1755007878146_905,
    output logic [3:0] inj_out_case_casez_1755007878146_901,
    output logic [7:0] inj_out_reg_p_1755007878145_773,
    output logic [7:0] inj_out_val_o_1755007878146_156,
    output logic [7:0] inj_out_w_1755007878147_599,
    output logic inj_task_output_valid_1755007878146_939,
    output logic inj_valid_out_1755007878145_380
);
    // BEGIN: split_basic_blocking_ts1755007878145
    // BEGIN: CaseStatementConditions_ts1755007878147
    // BEGIN: basic_assign_if_ts1755007878147
    logic intermediate_wire_ts1755007878147;
        // BEGIN: mod_simple_ts1755007878149
        assign inj_out_1755007878149_301 = reset;
        // END: mod_simple_ts1755007878149

        mod_name_conflict mod_name_conflict_inst_1755007878148_427 (
            .in_a(inj_in_b_1755007878147_914),
            .out_a(inj_out_a_1755007878148_894)
        );
    assign intermediate_wire_ts1755007878147 = inj_condition_p_1755007878145_613 & inj_in_b_1755007878147_914;
    always_comb begin
        if (intermediate_wire_ts1755007878147) begin
            inj_out_c_1755007878147_795 = 1'b1;
        end else begin
            inj_out_c_1755007878147_795 = 1'b0;
        end
    end
    // END: basic_assign_if_ts1755007878147

    split_case split_case_inst_1755007878147_6454 (
        .d0_w(inj_in_true_o_1755007878146_651),
        .d1_w(inj_d1_w_1755007878147_154),
        .d2_w(inj_d2_w_1755007878147_856),
        .d3_w(inj_in_val_p_1755007878145_378),
        .sel_w(inj_sel_in_1755007878146_174),
        .out_w(inj_out_w_1755007878147_599),
        .clk_w(clk)
    );
    always_comb begin
        case (inj_selector_1755007878146_468)
            2'b00: inj_out_case_case_1755007878146_397 = inj_data_c_1755007878146_599;
            2'b01: inj_out_case_case_1755007878146_397 = inj_data_c_1755007878146_599 + 1;
            2'b10: inj_out_case_case_1755007878146_397 = inj_data_c_1755007878146_599 + 2;
            default: inj_out_case_case_1755007878146_397 = 4'bxxxx;
        endcase
        casez (inj_selector_1755007878146_468)
            2'b0?: inj_out_case_casez_1755007878146_901 = inj_data_c_1755007878146_599 + 10;
            2'b1?: inj_out_case_casez_1755007878146_901 = inj_data_c_1755007878146_599 + 20;
            default: inj_out_case_casez_1755007878146_901 = 4'bzzzz;
        endcase
        casex (inj_selector_1755007878146_468)
            2'b0?: inj_out_case_casex_1755007878146_905 = inj_data_c_1755007878146_599 - 1;
            2'b1?: inj_out_case_casex_1755007878146_905 = inj_data_c_1755007878146_599 - 2;
            default: inj_out_case_casex_1755007878146_905 = 4'bxxxx;
        endcase
    end
    // END: CaseStatementConditions_ts1755007878147

    module_task_write module_task_write_inst_1755007878146_785 (
        .task_en(inj_condition_p_1755007878145_613),
        .task_output_valid(inj_task_output_valid_1755007878146_939),
        .in_task_data(inj_in_true_o_1755007878146_651)
    );
    case_selector case_selector_inst_1755007878146_6307 (
        .data_out_case(inj_data_out_case_1755007878146_672),
        .data0(inj_data0_1755007878146_473),
        .data1(inj_data1_1755007878146_259),
        .data2(inj_data2_1755007878146_67),
        .data3(inj_data3_1755007878146_54),
        .sel_in(inj_sel_in_1755007878146_174)
    );
    recursive_macro_dummy recursive_macro_dummy_inst_1755007878146_4336 (
        .in_bit(inj_condition_p_1755007878145_613),
        .out_bit(inj_out_bit_1755007878146_291)
    );
    split_conditional_blocking split_conditional_blocking_inst_1755007878146_2904 (
        .in_true_o(inj_in_true_o_1755007878146_651),
        .out_val_o(inj_out_val_o_1755007878146_156),
        .condition_o(inj_condition_p_1755007878145_613),
        .in_false_o(inj_in_val_p_1755007878145_378)
    );
    always @(*) begin
        inj_out1_a_1755007878145_289 = inj_in_val_p_1755007878145_378;
    end
    // END: split_basic_blocking_ts1755007878145

    ModuleWithInterface ModuleWithInterface_inst_1755007878145_2233 (
        .valid_out(inj_valid_out_1755007878145_380),
        .clk_in(clk)
    );
    split_if_empty_then split_if_empty_then_inst_1755007878145_158 (
        .out_reg_p(inj_out_reg_p_1755007878145_773),
        .clk_p(clk),
        .condition_p(inj_condition_p_1755007878145_613),
        .in_val_p(inj_in_val_p_1755007878145_378)
    );
endmodule

