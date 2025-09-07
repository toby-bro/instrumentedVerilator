interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module HandleOutOfBoundsRead (
    input logic [3:0] i_addr_arr,
    input logic [3:0] i_addr_sel,
    input logic [7:0] i_vector,
    output logic [7:0] o_array_var_elem,
    output logic o_sel_var_bit
);
    parameter ARR_SIZE = 4;
    logic [7:0] my_array [0:ARR_SIZE-1];
    assign my_array[0] = 8'd10;
    assign my_array[1] = 8'd20;
    assign my_array[2] = 8'd30;
    assign my_array[3] = 8'd40;
    assign o_sel_var_bit = i_vector[i_addr_sel];
    assign o_array_var_elem = my_array[i_addr_arr];
endmodule

module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_data1_1755007822494_499,
    input int inj_data_in_1755007822495_212,
    input logic [3:0] inj_i_addr_arr_1755007822493_669,
    input logic [3:0] inj_i_addr_sel_1755007822493_212,
    input logic [7:0] inj_in_task_data_1755007822492_37,
    input logic inj_sel_1755007822494_85,
    input logic inj_task_en_1755007822492_954,
    input wire reset,
    output int inj_data_out_1755007822495_282,
    output logic [7:0] inj_o_array_var_elem_1755007822493_400,
    output logic inj_o_sel_var_bit_1755007822493_9,
    output logic inj_result_1755007822494_848,
    output logic inj_sub_out_1755007822493_706,
    output logic inj_task_output_valid_1755007822492_338
);
    // BEGIN: module_task_write_ts1755007822492
    // BEGIN: sub_module_ts1755007822493
    // BEGIN: multiplexer_2to1_ts1755007822494
    mod_named_begin mod_named_begin_inst_1755007822495_6154 (
        .data_out(inj_data_out_1755007822495_282),
        .data_in(inj_data_in_1755007822495_212)
    );
    assign inj_result_1755007822494_848 = inj_sel_1755007822494_85 ? inj_data1_1755007822494_499 : inj_task_en_1755007822492_954;
    // END: multiplexer_2to1_ts1755007822494

    assign inj_sub_out_1755007822493_706 = !inj_task_en_1755007822492_954;
    // END: sub_module_ts1755007822493

    HandleOutOfBoundsRead HandleOutOfBoundsRead_inst_1755007822493_1791 (
        .o_array_var_elem(inj_o_array_var_elem_1755007822493_400),
        .o_sel_var_bit(inj_o_sel_var_bit_1755007822493_9),
        .i_addr_arr(inj_i_addr_arr_1755007822493_669),
        .i_addr_sel(inj_i_addr_sel_1755007822493_212),
        .i_vector(inj_in_task_data_1755007822492_37)
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
        update_vif_signals(inj_task_en_1755007822492_954, inj_in_task_data_1755007822492_37, task_vif_inst.data, task_vif_inst.valid, task_vif_inst.ready);
        inj_task_output_valid_1755007822492_338 = task_vif_inst.valid;
    end
    // END: module_task_write_ts1755007822492
endmodule

