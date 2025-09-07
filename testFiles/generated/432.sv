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

module child_packed_scalar_port (
    input logic [3:0] data_in,
    output logic [3:0] data_out
);
    assign data_out = data_in;
endmodule

module m_driver_check (
    input bit clk,
    input int val_in,
    output int driven_var
);
    int my_driven_var;
    function automatic void write_to_var(input int val);
        my_driven_var = val;
    endfunction
    always @(posedge clk) begin
        write_to_var(val_in);
    end
    assign driven_var = my_driven_var;
endmodule

module module_sequential_writes (
    input logic [7:0] addr,
    input logic [7:0] wdata,
    output logic write_status
);
    my_if vif_bus();
    always_comb begin
        vif_bus.data = wdata;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        write_status = vif_bus.ready;
    end
endmodule

module split_input_only_var (
    input logic clk_k,
    input logic control_signal_k,
    input logic [7:0] data_in_k,
    output logic [7:0] data_out_k
);
    always @(posedge clk_k) begin
        if (control_signal_k) begin
            data_out_k <= data_in_k;
        end
    end
endmodule

module unreferenced_module (
    input logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_addr_1755007898674_847,
    input logic inj_control_signal_k_1755007898675_981,
    input logic [3:0] inj_data_in_1755007898673_838,
    input bit inj_in_1755007898678_299,
    input logic [31:0] inj_in_vec_1755007898673_415,
    input int inj_start_index_1755007898673_980,
    input logic [7:0] inj_wdata_1755007898674_852,
    input int inj_width_1755007898673_520,
    input wire reset,
    output logic [3:0] inj_data_out_1755007898673_391,
    output logic [7:0] inj_data_out_k_1755007898675_485,
    output int inj_driven_var_1755007898676_963,
    output logic inj_o_sum_1755007898675_163,
    output bit inj_out_1755007898678_738,
    output logic [7:0] inj_out_down_1755007898673_609,
    output logic [7:0] inj_out_up_1755007898673_854,
    output logic inj_unused_out_1755007898677_330,
    output logic [7:0] inj_wide_reg_1755007898675_564,
    output logic inj_write_status_1755007898674_671
);
    // BEGIN: range_select_indexed_packed_ts1755007898674
    // BEGIN: mod_lint_target_ts1755007898675
    logic l_reg_ts1755007898675;
        BindSimpleModule BindSimpleModule_inst_1755007898678_4940 (
            .out(inj_out_1755007898678_738),
            .in(inj_in_1755007898678_299)
        );
        unreferenced_module unreferenced_module_inst_1755007898677_9567 (
            .unused_out(inj_unused_out_1755007898677_330),
            .unused_in(l_reg_ts1755007898675)
        );
        m_driver_check m_driver_check_inst_1755007898676_4245 (
            .clk(clk),
            .val_in(inj_width_1755007898673_520),
            .driven_var(inj_driven_var_1755007898676_963)
        );
    always_comb begin
        l_reg_ts1755007898675 = 1;
        inj_wide_reg_1755007898675_564 = {clk, reset};
    end
    assign inj_o_sum_1755007898675_163 = clk + reset;
    // END: mod_lint_target_ts1755007898675

    split_input_only_var split_input_only_var_inst_1755007898675_2601 (
        .data_in_k(inj_addr_1755007898674_847),
        .data_out_k(inj_data_out_k_1755007898675_485),
        .clk_k(clk),
        .control_signal_k(inj_control_signal_k_1755007898675_981)
    );
    module_sequential_writes module_sequential_writes_inst_1755007898674_2863 (
        .wdata(inj_wdata_1755007898674_852),
        .write_status(inj_write_status_1755007898674_671),
        .addr(inj_addr_1755007898674_847)
    );
    always_comb begin
        if (inj_start_index_1755007898673_980 >= 0 && inj_width_1755007898673_520 > 0 && inj_start_index_1755007898673_980 + inj_width_1755007898673_520 <= 32) begin
            case (inj_width_1755007898673_520)
                1: inj_out_up_1755007898673_854 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 +: 1];
                2: inj_out_up_1755007898673_854 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 +: 2];
                4: inj_out_up_1755007898673_854 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 +: 4];
                8: inj_out_up_1755007898673_854 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 +: 8];
                default: inj_out_up_1755007898673_854 = 'x;
            endcase
        end else begin
            inj_out_up_1755007898673_854 = 'x;
        end
        if (inj_start_index_1755007898673_980 >= inj_width_1755007898673_520 - 1 && inj_width_1755007898673_520 > 0 && inj_start_index_1755007898673_980 < 32) begin
            case (inj_width_1755007898673_520)
                1: inj_out_down_1755007898673_609 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 -: 1];
                2: inj_out_down_1755007898673_609 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 -: 2];
                4: inj_out_down_1755007898673_609 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 -: 4];
                8: inj_out_down_1755007898673_609 = inj_in_vec_1755007898673_415[inj_start_index_1755007898673_980 -: 8];
                default: inj_out_down_1755007898673_609 = 'x;
            endcase
        end else begin
            inj_out_down_1755007898673_609 = 'x;
        end
    end
    // END: range_select_indexed_packed_ts1755007898674

    child_packed_scalar_port child_packed_scalar_port_inst_1755007898673_6394 (
        .data_out(inj_data_out_1755007898673_391),
        .data_in(inj_data_in_1755007898673_838)
    );
endmodule

