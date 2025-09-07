module named_begin_example (
    input  logic [7:0] a,
    output logic [7:0] y
);
    always_comb begin : blk_outer
        logic [7:0] tmp;
        begin : blk_inner
            tmp = a + 1;
        end : blk_inner
        y = tmp;
    end : blk_outer
endmodule
module foreach_fixed (
    input  logic [7:0] din,
    output logic [7:0] sum
);
    logic [7:0] arr [0:3];
    int i;
    always_comb begin
        arr[0] = din;
        arr[1] = din + 1;
        arr[2] = din + 2;
        arr[3] = din + 3;
        sum = 0;
        foreach (arr[i]) begin : loop_blk
            sum += arr[i];
        end
    end
endmodule
module foreach_dynamic (
    input  logic [7:0] din,
    output logic [7:0] out_sum
);
    function automatic int accumulate(input int val);
        static int state = 0;
        begin : f_block
            state += val;
            accumulate = state;
        end
    endfunction
    always_comb begin : dyn_loop
        automatic int dyn_arr[];      
        int idx;
        dyn_arr = new[4];
        dyn_arr[0] = accumulate(din);
        dyn_arr[1] = accumulate(din + 1);
        dyn_arr[2] = accumulate(din + 2);
        dyn_arr[3] = accumulate(din + 3);
        out_sum = 0;
        foreach (dyn_arr[idx]) begin
            out_sum += dyn_arr[idx];
        end
    end
endmodule
module foreach_assoc (
    input  logic dummy_in,           
    output logic [31:0] count
);
    typedef int aa_t [string];
    string key;
    always_comb begin
        aa_t assoc;
        assoc["a"] = 1;
        assoc["b"] = 2;
        assoc["c"] = 3;
        count = 0;
        foreach (assoc[key]) begin : assoc_loop
            count += assoc[key];
        end
    end
endmodule
module func_static (
    input  logic [3:0] a,
    output logic [3:0] y
);
    function automatic [3:0] inc_static(input [3:0] in);
        static logic [3:0] s = 0;
        begin : fn_block
            s = s + in;
            inc_static = s;
        end
    endfunction
    always_comb begin
        y = inc_static(a);
    end
endmodule
module deep_if (
    input  logic [3:0] sel,
    output logic       flag
);
    always_comb begin
        flag = 0;
        if (sel[3]) begin
            if (sel[2]) begin
                if (sel[1]) begin
                    if (sel[0]) begin
                        flag = 1;
                    end
                end
            end
        end
    end
endmodule
module typedef_example (
    input  logic [7:0] in,
    output logic [7:0] out
);
    always_comb begin : blk_typedef
        typedef struct packed {
            logic [7:0] a;
            logic [7:0] b;
        } pair_t;
        pair_t p;
        p.a = in;
        p.b = in + 1;
        out = p.a + p.b;
    end
endmodule
module unique_if_example (
    input  logic [1:0] sel,
    output logic [7:0] y
);
    always_comb begin
        unique if (sel == 2'b00) begin
            y = 0;
        end else if (sel == 2'b01) begin
            y = 1;
        end else if (sel == 2'b10) begin
            y = 2;
        end else begin
            y = 3;
        end
    end
endmodule
module task_example (
    input  logic [7:0] in,
    output logic [7:0] out
);
    task automatic compute(input logic [7:0] v, output logic [7:0] result);
        begin : task_block
            result = v + 8;
        end
    endtask
    always_comb begin
        compute(in, out);
    end
endmodule
