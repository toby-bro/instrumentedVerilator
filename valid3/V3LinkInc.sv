module mod_stmt_prepost (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    logic [7:0] reg_q, reg_d;
    always_comb begin
        reg_d = reg_q;
        if (rst) begin
            reg_d = in_data;
        end else begin
            reg_d++;
            --reg_d;
        end
    end
    always_ff @(posedge clk) reg_q <= reg_d;
    assign out_data = reg_q;
endmodule
module mod_expr_prepost (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_sum
);
    logic [7:0] a_q, a_d;
    logic [7:0] b_q, b_d;
    always_comb begin
        a_d = a_q;
        b_d = b_q;
        if (rst) begin
            a_d = in_data;
            b_d = 0;
        end else begin
            b_d = a_d++ + ++a_d;
        end
    end
    always_ff @(posedge clk) begin
        a_q <= a_d;
        b_q <= b_d;
    end
    assign out_sum = b_q;
endmodule
module mod_arr_sel_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic [1:0]  idx_in,
    output logic [7:0]  sum_out
);
    logic [1:0] idx_q, idx_d;
    logic [7:0] arr_q [0:3];
    logic [7:0] arr_d [0:3];
    always_comb begin
        for (int k = 0; k < 4; k++) arr_d[k] = arr_q[k];
        idx_d = idx_q;
        if (rst) begin
            idx_d = idx_in;
            arr_d[0] = 8'd0;
            arr_d[1] = 8'd1;
            arr_d[2] = 8'd2;
            arr_d[3] = 8'd3;
        end else begin
            arr_d[idx_q]++;
            idx_d++;
            --arr_d[0];
        end
    end
    always_ff @(posedge clk) begin
        idx_q <= idx_d;
        for (int k = 0; k < 4; k++) arr_q[k] <= arr_d[k];
    end
    assign sum_out = arr_q[0] + arr_q[1] + arr_q[2] + arr_q[3];
endmodule
module mod_task_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in_val,
    output logic [7:0]  out_val
);
    logic [7:0] temp_q, temp_d;
    task automatic do_ops (inout logic [7:0] v);
        v = ++v;
        v = v--;
    endtask
    always_comb begin
        temp_d = temp_q;
        if (rst) temp_d = in_val;
        else     do_ops(temp_d);
    end
    always_ff @(posedge clk) temp_q <= temp_d;
    assign out_val = temp_q;
endmodule
module mod_while_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  in_cnt,
    output logic [7:0]  out_cnt
);
    logic [3:0] i_q, i_d;
    logic [7:0] counter_q, counter_d;
    always_comb begin
        i_d = i_q;
        counter_d = counter_q;
        int j = 0;
        if (rst) begin
            i_d = in_cnt;
            counter_d = 0;
            j = 0;
        end else begin
            j = i_d;
            while (j != 0) begin
                j--;
                counter_d++;
            end
            i_d = 0;
        end
    end
    always_ff @(posedge clk) begin
        i_q       <= i_d;
        counter_q <= counter_d;
    end
    assign out_cnt = counter_q;
endmodule
module mod_cond_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic        sel,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic [7:0] a_q, a_d;
    logic [7:0] b_q, b_d;
    logic [7:0] d_q, d_d;
    always_comb begin
        a_d = a_q;
        b_d = b_q;
        d_d = d_q;
        if (rst) begin
            a_d = data_in;
            b_d = data_in;
            d_d = 0;
        end else begin
            if (sel) begin
                d_d = a_d++;
            end else begin
                d_d = b_d++;
            end
        end
    end
    always_ff @(posedge clk) begin
        a_q <= a_d;
        b_q <= b_d;
        d_q <= d_d;
    end
    assign data_out = d_q;
endmodule
module mod_logical_and (
    input  logic        clk,
    input  logic        rst,
    input  logic        cond_in,
    output logic        flag
);
    logic [7:0] val_q, val_d;
    logic       flag_q, flag_d;
    always_comb begin
        val_d  = val_q;
        flag_d = flag_q;
        if (rst) begin
            val_d  = 0;
            flag_d = 0;
        end else begin
            val_d++;
            flag_d = (cond_in && (val_d != 0));
        end
    end
    always_ff @(posedge clk) begin
        val_q  <= val_d;
        flag_q <= flag_d;
    end
    assign flag = flag_q;
endmodule
module mod_foreach_inc (
    input  logic        clk,
    input  logic        rst,
    output logic [31:0] sum_out
);
    logic [7:0]  arr_q [0:7];
    logic [7:0]  arr_d [0:7];
    logic [31:0] sum_q, sum_d;
    always_comb begin
        for (int m = 0; m < 8; m++) arr_d[m] = arr_q[m];
        sum_d = sum_q;
        if (rst) begin
            for (int ii = 0; ii < 8; ii++) arr_d[ii] = ii[7:0];
            sum_d = 0;
        end else begin
            foreach (arr_d[i]) arr_d[i]++;
            sum_d = 0;
            foreach (arr_d[j]) sum_d = sum_d + arr_d[j];
        end
    end
    always_ff @(posedge clk) begin
        for (int m = 0; m < 8; m++) arr_q[m] <= arr_d[m];
        sum_q <= sum_d;
    end
    assign sum_out = sum_q;
endmodule
module mod_case_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic [1:0]  sel,
    output logic [7:0]  out_val
);
    logic [7:0] base_q, base_d;
    logic [7:0] out_q,  out_d;
    always_comb begin
        base_d = base_q;
        out_d  = out_q;
        if (rst) begin
            base_d = 0;
            out_d  = 0;
        end else begin
            logic [7:0] base_work;
            base_work = base_q;
            case (sel)
                2'b00: base_work = base_work++;
                2'b01: base_work = ++base_work;
                default: base_work = --base_work;
            endcase
            base_d = base_work;
            out_d  = base_d;
        end
    end
    always_ff @(posedge clk) begin
        base_q <= base_d;
        out_q  <= out_d;
    end
    assign out_val = out_q;
endmodule
module mod_wait_inc (
    input  logic        clk,
    input  logic        rst,
    input  logic        trigger,
    input  logic        done_in,
    output logic [7:0]  count_out
);
    logic [7:0] count;
    always @(posedge clk) begin
        if (rst) begin
            count <= 0;
        end else if (trigger) begin
            wait (done_in);
            count <= count + 8'd1;
        end
    end
    assign count_out = count;
endmodule
module mod_event_control (
    input  logic        clk,
    input  logic        rst,
    input  logic        send,
    output logic [7:0]  count_out
);
    event e;
    logic [7:0] count_q;
    always_ff @(posedge clk) begin
        if (rst) count_q <= 0;
        else if (send) -> e;
    end
    always @(e) count_q <= count_q + 8'd1;
    assign count_out = count_q;
endmodule
module mod_logical_eq (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in_a,
    input  logic [7:0]  in_b,
    output logic        result
);
    logic [7:0] local_a_q, local_a_d;
    logic       res_q, res_d;
    always_comb begin
        local_a_d = local_a_q;
        res_d     = res_q;
        if (rst) begin
            local_a_d = in_a;
            res_d     = 0;
        end else begin
            res_d = (local_a_q == in_b);
            local_a_d++;
        end
    end
    always_ff @(posedge clk) begin
        local_a_q <= local_a_d;
        res_q     <= res_d;
    end
    assign result = res_q;
endmodule
