interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
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

module unknown_class_pkg_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007803222_105,
    input logic [3:0] inj_case_inside_val_1755007803229_362,
    input logic [7:0] inj_data_case_a_1755007803222_377,
    input logic [7:0] inj_data_case_b_1755007803222_49,
    input logic inj_in1_1755007803224_249,
    input int inj_in_val_1755007803222_437,
    input logic [1:0] inj_select_case_1755007803222_921,
    input wire reset,
    output logic inj_case_output_ready_1755007803222_400,
    output logic inj_dummy_out_non_ansi_1755007803225_30,
    output logic [4:0] inj_internal_out_1755007803229_194,
    output logic inj_named_conn_out_1755007803225_241,
    output logic inj_out_1755007803224_408,
    output logic inj_out_a_1755007803222_966,
    output int inj_out_b_1755007803222_517,
    output logic [1:0] inj_out_bits_1755007803223_179,
    output int inj_out_val_1755007803222_429,
    output logic [7:0] inj_out_x_j_1755007803227_997,
    output logic [7:0] inj_out_y_j_1755007803227_106,
    output logic inj_result_1755007803226_59
);
    // BEGIN: module_case_write_ts1755007803223
    // BEGIN: cast_select_demo_ts1755007803223
    logic [7:0] internal_ts1755007803223;
        // BEGIN: explicit_non_ansi_ports_module_ts1755007803225
        input logic inj_in1_1755007803224_249_ts1755007803225;
        output logic inj_named_conn_out_1755007803225_241_ts1755007803225;
        input logic inj_a_1755007803222_105_ts1755007803225;
        output logic inj_dummy_out_non_ansi_1755007803225_30_ts1755007803225;
            // BEGIN: case_unique_casez_reordered_mod_ts1755007803229
            always @* begin
                unique casez ({inj_select_case_1755007803222_921[0], inj_case_inside_val_1755007803229_362[3:2], inj_select_case_1755007803222_921[1]})
                    4'b1?0?: inj_internal_out_1755007803229_194 = 30;
                    4'b?101: inj_internal_out_1755007803229_194 = 31;  
                    4'b0?1?: inj_internal_out_1755007803229_194 = 32;
                    4'b1?1?: inj_internal_out_1755007803229_194 = 33;  
                    4'b?111: inj_internal_out_1755007803229_194 = 34;  
                endcase
            end
            // END: case_unique_casez_reordered_mod_ts1755007803229

            split_multiple_in_branch split_multiple_in_branch_inst_1755007803227_7369 (
                .in_a_j(internal_ts1755007803223),
                .in_b_j(inj_data_case_a_1755007803222_377),
                .out_x_j(inj_out_x_j_1755007803227_997),
                .out_y_j(inj_out_y_j_1755007803227_106),
                .clk_j(clk),
                .condition_j(inj_a_1755007803222_105)
            );
            // BEGIN: multiplexer_2to1_ts1755007803226
            assign inj_result_1755007803226_59 = inj_a_1755007803222_105_ts1755007803225 ? inj_a_1755007803222_105 : inj_in1_1755007803224_249;
            // END: multiplexer_2to1_ts1755007803226

        assign inj_named_conn_out_1755007803225_241_ts1755007803225 = inj_in1_1755007803224_249_ts1755007803225;
        assign inj_dummy_out_non_ansi_1755007803225_30_ts1755007803225 = inj_a_1755007803222_105_ts1755007803225;
        // END: explicit_non_ansi_ports_module_ts1755007803225

        // BEGIN: simple_xor_gate_ts1755007803224
        assign inj_out_1755007803224_408 = inj_in1_1755007803224_249 ^ inj_a_1755007803222_105;
        // END: simple_xor_gate_ts1755007803224

    always_comb begin
        internal_ts1755007803223 = inj_data_case_b_1755007803222_49;
        inj_out_bits_1755007803223_179 = internal_ts1755007803223[3 -: 2];
    end
    // END: cast_select_demo_ts1755007803223

    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755007803222_921)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = inj_data_case_a_1755007803222_377;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755007803222_49;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755007803222_400 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755007803223

    ModuleBasic ModuleBasic_inst_1755007803222_6311 (
        .out_a(inj_out_a_1755007803222_966),
        .out_b(inj_out_b_1755007803222_517),
        .a(inj_a_1755007803222_105),
        .b(inj_in_val_1755007803222_437)
    );
    unknown_class_pkg_diag_mod unknown_class_pkg_diag_mod_inst_1755007803222_9880 (
        .out_val(inj_out_val_1755007803222_429),
        .in_val(inj_in_val_1755007803222_437)
    );
endmodule

