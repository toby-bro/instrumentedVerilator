module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

module buf_primitive (
    input wire i,
    output wire o
);
    buf b1 (o, i);
endmodule

module mod_split_multiple_vars (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_mv_a,
    output logic [7:0] out_mv_b,
    output logic [7:0] out_mv_c
);
    logic [7:0]  split_mv_var;
    logic [7:0] other_mv_var1;
    logic [7:0] other_mv_var2;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var <= 8'b0;
            other_mv_var1 <= 8'b0;
            other_mv_var2 <= 8'b0;
        end else begin
            split_mv_var <= data_in;
            other_mv_var1 <= data_in + 1;
            other_mv_var2 <= data_in + 2;
            if (data_in > 100) begin
                split_mv_var <= 8'hFF;
            end
            out_mv_a <= split_mv_var;
            out_mv_b <= other_mv_var1;
            out_mv_c <= other_mv_var2;
        end
    end
endmodule

module split_nested_if (
    input logic clk_m,
    input logic cond1_m,
    input logic cond2_m,
    input logic [7:0] val_a_m,
    input logic [7:0] val_b_m,
    input logic [7:0] val_c_m,
    output logic [7:0] result_m
);
    always @(posedge clk_m) begin
        if (cond1_m) begin
            if (cond2_m) begin
                result_m <= val_a_m;
            end else begin
                result_m <= val_b_m;
            end
        end else begin
            result_m <= val_c_m;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_arg_in_task_1755007863434_961,
    input logic inj_cond2_m_1755007863436_210,
    input logic [7:0] inj_data_a_init_task_1755007863434_282,
    input logic [15:0] inj_in_data_1755007863434_325,
    input logic inj_start_task_1755007863434_563,
    input wire reset,
    output logic [7:0] inj_data_a_out_task_1755007863434_524,
    output logic [7:0] inj_data_b_out_task_1755007863434_487,
    output logic [7:0] inj_data_out_1755007863437_940,
    output wire inj_o_1755007863434_761,
    output logic [7:0] inj_out_field_a_1755007863434_915,
    output logic [7:0] inj_out_field_b_1755007863434_613,
    output logic [7:0] inj_out_mv_a_1755007863436_408,
    output logic [7:0] inj_out_mv_b_1755007863436_814,
    output logic [7:0] inj_out_mv_c_1755007863436_228,
    output logic [7:0] inj_result_m_1755007863436_75
);
    // BEGIN: module_task_args_ts1755007863435
    logic [7:0] data_a_ts1755007863435 ;
    logic [7:0] data_b_ts1755007863435 ;
        // BEGIN: cu_base_ts1755007863438
        assign inj_data_out_1755007863437_940 = inj_data_a_init_task_1755007863434_282;
        // END: cu_base_ts1755007863438

        split_nested_if split_nested_if_inst_1755007863436_3286 (
            .val_a_m(inj_arg_in_task_1755007863434_961),
            .val_b_m(data_a_ts1755007863435),
            .val_c_m(inj_data_a_init_task_1755007863434_282),
            .result_m(inj_result_m_1755007863436_75),
            .clk_m(clk),
            .cond1_m(inj_start_task_1755007863434_563),
            .cond2_m(inj_cond2_m_1755007863436_210)
        );
        mod_split_multiple_vars mod_split_multiple_vars_inst_1755007863436_9333 (
            .data_in(inj_data_a_init_task_1755007863434_282),
            .reset(reset),
            .out_mv_a(inj_out_mv_a_1755007863436_408),
            .out_mv_b(inj_out_mv_b_1755007863436_814),
            .out_mv_c(inj_out_mv_c_1755007863436_228),
            .clk(clk)
        );
    task automatic modify_vars;
        input logic [7:0] task_arg_ts1755007863435;
        logic [7:0] task_local_ts1755007863435 ;
        begin
            task_local_ts1755007863435 = task_arg_ts1755007863435;
            data_a_ts1755007863435 = task_local_ts1755007863435 + 8'd1;
            data_b_ts1755007863435 = task_arg_ts1755007863435 - 8'd1;
        end
    endtask
    always_comb begin
        if (inj_start_task_1755007863434_563) begin
            data_a_ts1755007863435 = inj_data_a_init_task_1755007863434_282;
            data_b_ts1755007863435 = 8'hFF;
            modify_vars(inj_arg_in_task_1755007863434_961);
        end else begin
            data_a_ts1755007863435 = 8'h00;
            data_b_ts1755007863435 = 8'h00;
        end
    end
    always_comb begin
        inj_data_a_out_task_1755007863434_524 = data_a_ts1755007863435 + 8'd2;
        inj_data_b_out_task_1755007863434_487 = data_b_ts1755007863435;
    end
    // END: module_task_args_ts1755007863435

    buf_primitive buf_primitive_inst_1755007863434_1040 (
        .o(inj_o_1755007863434_761),
        .i(clk)
    );
    StructExample StructExample_inst_1755007863434_2918 (
        .out_field_a(inj_out_field_a_1755007863434_915),
        .out_field_b(inj_out_field_b_1755007863434_613),
        .in_data(inj_in_data_1755007863434_325)
    );
endmodule

