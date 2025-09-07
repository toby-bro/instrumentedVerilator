module module_forceable_attr (
    input wire i_clk,
    input logic i_data_in,
    input wire i_rst_n,
    input logic i_write_en,
    input logic [7:0] inj_data_in_1755538562805_744,
    input wire [3:0] inj_data_in_1755538562806_247,
    input wire [1:0] inj_sel_1755538562806_778,
    output reg [3:0] inj_case_out_1755538562806_728,
    output logic inj_is_even_1755538562805_450,
    output logic o_forceable_signal,
    output logic o_read_signal
);
    logic forceable_signal ;
    logic read_internal;
        // BEGIN: CaseZExample_ts1755538562806
        wire [3:0] local_data_ts1755538562806;
        assign local_data_ts1755538562806 = inj_data_in_1755538562806_247;
        always @* begin
            casez (inj_sel_1755538562806_778)
                2'b0?: inj_case_out_1755538562806_728 = local_data_ts1755538562806;
                2'b10: inj_case_out_1755538562806_728 = 4'b1111;
                default: inj_case_out_1755538562806_728 = 4'b0000;
            endcase
        end
        // END: CaseZExample_ts1755538562806

        // BEGIN: FunctionTaskMod_ts1755538562805
        function automatic bit check_even(input logic [7:0] v);
            check_even = ~v[0];
        endfunction
        task automatic dummy_task(input logic [7:0] v);
            int tmp_ts1755538562805;
            tmp_ts1755538562805 = v;
        endtask
        assign inj_is_even_1755538562805_450 = check_even(inj_data_in_1755538562805_744);
        // END: FunctionTaskMod_ts1755538562805

    assign o_forceable_signal = forceable_signal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            forceable_signal <= 1'b0;
            read_internal <= 1'b0;
        end else begin
            if (i_write_en) begin
                forceable_signal <= i_data_in;
            end
            read_internal <= forceable_signal;
        end
    end
    assign o_read_signal = read_internal;
endmodule

