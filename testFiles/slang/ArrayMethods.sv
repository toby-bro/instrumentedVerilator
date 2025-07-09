module arr_reduction (
    input  logic        dummy_in,
    output logic [31:0] sum_out,
    output logic [31:0] prod_out,
    output logic [31:0] and_out,
    output logic [31:0] or_out,
    output logic [31:0] xor_out
);
    localparam int vals[5] = '{1, 2, 3, 4, 5};
    localparam int l_sum  = vals.sum();
    localparam int l_prod = vals.product();
    localparam int l_and  = vals.and();
    localparam int l_or   = vals.or();
    localparam int l_xor  = vals.xor();
    assign sum_out  = l_sum;
    assign prod_out = l_prod;
    assign and_out  = l_and;
    assign or_out   = l_or;
    assign xor_out  = l_xor;
endmodule
module arr_minmax_unique (
    input  logic        dummy_in,
    output logic [31:0] min_out,
    output logic [31:0] max_out,
    output logic [31:0] uniq_cnt_out,
    output logic [31:0] size_out
);
    localparam int data_a[7] = '{8, 3, 7, 9, 2, 3, 2};
    int uniq_q[$];
    int uniq_cnt;
    int min_val;
    int max_val;
    initial begin
        uniq_q   = data_a.unique();
        uniq_cnt = uniq_q.size();
        min_val  = data_a.min()[0];
        max_val  = data_a.max()[0];
        min_out      = min_val;
        max_out      = max_val;
        uniq_cnt_out = uniq_cnt;
        size_out     = 7;
    end
endmodule
module dyn_sort_reverse (
    input  logic        clk,
    input  logic        trigger,
    output logic [31:0] first_after_sort,
    output logic [31:0] first_after_reverse
);
    int   dyn_arr[];
    int   first_sort_reg;
    int   first_rev_reg;
    logic init_done;
    always_ff @(posedge clk) begin
        if (!init_done) begin
            dyn_arr = new[5];
            foreach (dyn_arr[i])
                dyn_arr[i] = 5 - i;
            first_sort_reg <= 0;
            first_rev_reg  <= 0;
            init_done      <= 1;
        end
        else if (trigger) begin
            dyn_arr.reverse();
            first_rev_reg  <= dyn_arr[0];
            dyn_arr.sort();
            first_sort_reg <= dyn_arr[0];
        end
    end
    assign first_after_sort    = first_sort_reg;
    assign first_after_reverse = first_rev_reg;
endmodule
module queue_operations (
    input  logic        clk,
    input  logic [31:0] in_data,
    input  logic        do_push,
    input  logic        do_pop,
    input  logic        do_insert,
    input  logic        do_delete,
    output logic [31:0] popped_value,
    output logic [31:0] queue_size
);
    int q[$:8];
    always_ff @(posedge clk) begin
        if (do_push)
            q.push_back(in_data);
        if (do_insert)
            q.insert(0, 99);
        if (do_delete && q.size() > 0)
            q.delete(0);
        if (do_pop && q.size() > 0)
            popped_value <= q.pop_front();
        queue_size <= q.size();
    end
endmodule
module assoc_array_methods (
    input  logic        clk,
    input  logic        trigger,
    output logic        exists_flag,
    output logic [31:0] num_out
);
    typedef int aa_t[string];
    aa_t aa;
    always @(posedge clk) begin
        if (trigger) begin
            aa["alpha"] = 11;
            aa["beta"]  = 22;
            exists_flag <= aa.exists("alpha");
            num_out     <= aa.num();
            aa.delete("beta");
        end
    end
endmodule
module dyn_array_delete (
    input  logic        clk,
    input  logic        do_clear,
    output logic [31:0] dyn_size
);
    int   dyn_data[];
    logic init_done;
    always @(posedge clk) begin
        if (!init_done) begin
            dyn_data = new[4];
            dyn_data = '{10, 20, 30, 40};
            init_done <= 1;
        end
        else begin
            if (do_clear)
                dyn_data.delete();
        end
        dyn_size <= dyn_data.size();
    end
endmodule
