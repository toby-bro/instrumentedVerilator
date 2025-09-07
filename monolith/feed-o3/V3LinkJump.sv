module debug_mod(input  logic [7:0] in, output logic [7:0] out);
    function automatic int f(input int v);
        int s;
        begin : repeat_block
            s = 0;
            repeat (v) begin
                s += 1;
                if (s > 4) break;
            end
        end
        return s;
    endfunction
    assign out = f(in)[7:0];
endmodule
module dumpTreeLevel_mod(input  logic [7:0] in, output logic [7:0] out);
    logic [7:0] arr [0:7];
    function automatic int sum_array();
        int i, s;
        s = 0;
        foreach (arr[i]) begin
            arr[i] = i;
            s += arr[i];
        end
        return s;
    endfunction
    assign out = sum_array()[7:0];
endmodule
module dumpTreeJsonLevel_mod(input  logic [7:0] in, output logic [7:0] out);
    function automatic int g(input int v);
        int count;
        count = 0;
        do begin
            count++;
        end while (count < v);
        return count;
    endfunction
    assign out = g(in)[7:0];
endmodule
module dumpTreeEitherLevel_mod(input  logic [7:0] in, output logic [7:0] out);
    function automatic int h(input int v);
        int c;
        c = 0;
        while (c < v) begin
            c++;
            if (c & 1) continue;
            c++;
        end
        return c;
    endfunction
    assign out = h(in)[7:0];
endmodule
module findAddLabel_mod(input  logic [7:0] in, output logic done);
    task automatic t;
        int idx;
        begin : my_block
            idx = 0;
            while (idx < in) begin
                idx++;
                if (idx == 3) disable my_block;
            end
        end
    endtask
    assign done = 1'b0;
endmodule
module addPrefixBlocks_mod(input  logic [3:0] a, output logic [3:0] b);
    always_comb begin : blk_outer
        begin : blk_inner
            b = a;
        end
    end
endmodule
module visitNodeModule_mod(input  logic [7:0] i, output logic [7:0] o);
    function automatic int calc(input int v);
        int sum, idx;
        sum = 0;
        for (idx = 0; idx < v; idx++) begin
            sum += idx;
        end
        return sum;
    endfunction
    assign o = calc(i)[7:0];
endmodule
module visitNodeFTask_mod(input  logic [7:0] x, output logic y);
    task automatic do_something(input int lim, output int res);
        int i;
        res = 0;
        for (i = 0; i < lim; i++) begin
            if (i > 5) return;
            res += i;
        end
    endtask
    int tmp;
    always_comb begin
        do_something(x, tmp);
        y = tmp[0];
    end
endmodule
module visitNodeBlock_mod(input  logic clk, input  logic rst, output logic flag);
    reg internal;
    always @(posedge clk or posedge rst) begin : sync_block
        if (rst) begin
            internal <= 1'b0;
        end else begin
            internal <= 1'b1;
        end
    end
    assign flag = internal;
endmodule
module visitPragma_mod(input  logic [7:0] i, output logic [7:0] o);
    function automatic int fx(input int v);
        int j, sum;
        sum = 0;
        for (j = 0; j < 8; j++) begin
            sum += (v + j);
        end
        return sum;
    endfunction
    assign o = fx(i)[7:0];
endmodule
module visitRepeat_mod(input  logic [7:0] val, output logic [7:0] out);
    function automatic int rep(input int cnt);
        int k;
        k = 0;
        repeat (cnt) begin
            k++;
            if (k > 10) break;
        end
        return k;
    endfunction
    assign out = rep(val)[7:0];
endmodule
module visitWhile_mod(input  logic [7:0] i, output logic [7:0] o);
    function automatic int w(input int n);
        int c;
        c = 0;
        while (1) begin
            if (c >= n) break;
            c++;
        end
        return c;
    endfunction
    assign o = w(i)[7:0];
endmodule
module visitDoWhile_mod(input  logic [7:0] i, output logic [7:0] o);
    function automatic int dw(input int n);
        int c;
        c = 0;
        do begin
            c++;
            if (c < n) continue;
        end while (c < n);
        return c;
    endfunction
    assign o = dw(i)[7:0];
endmodule
module visitForeach_mod(input  logic [7:0] sel, output logic [7:0] out);
    logic [7:0] mem [0:15];
    function automatic int fe();
        int idx, sum;
        sum = 0;
        foreach (mem[idx]) begin
            mem[idx] = idx;
            if (idx == sel) break;
            sum += mem[idx];
        end
        return sum;
    endfunction
    assign out = fe()[7:0];
endmodule
module visitReturn_mod(input  logic [7:0] in, output logic [7:0] out);
    function automatic int ret(input int a);
        if (a == 0) return 0;
        return a + 1;
    endfunction
    assign out = ret(in)[7:0];
endmodule
module visitBreak_mod(input  logic [7:0] d, output logic [7:0] q);
    function automatic int brk(input int v);
        int idx;
        brk = 0;
        for (idx = 0; idx < 16; idx++) begin
            if (idx == v) break;
            brk += idx;
        end
        return brk;
    endfunction
    assign q = brk(d)[7:0];
endmodule
module visitContinue_mod(input  logic [7:0] din, output logic [7:0] dout);
    function automatic int cont(input int v);
        int idx, s;
        s = 0;
        for (idx = 0; idx < 16; idx++) begin
            if (idx == v) continue;
            s += idx;
        end
        return s;
    endfunction
    assign dout = cont(din)[7:0];
endmodule
module visitDisable_mod(input  logic [7:0] a, output logic ready);
    task automatic t2;
        fork : parallel_block
            begin : blk1
                int x;
                x = a;
            end
        join_none
        disable parallel_block;
    endtask
    assign ready = 1'b0;
endmodule
module visitVarRef_mod(input  logic [7:0] d, output logic [7:0] r);
    logic [7:0] idx;
    always_comb begin
        idx = 0;
        for (idx = 0; idx < d; idx++) begin
        end
        r = idx;
    end
endmodule
module visitConst_mod(input  logic [7:0] din, output logic [7:0] dout);
    assign dout = din + 8'd5;
endmodule
module visitGenericNode_mod(input  logic [7:0] i, output logic [7:0] o);
    always_comb begin : generic_named_block
        o = i;
    end
endmodule
module constructor_mod(input  logic [7:0] i, output logic [7:0] o);
    typedef struct packed { logic [3:0] a; logic [3:0] b; } my_t;
    function automatic my_t make(input logic [7:0] val);
        my_t tmp;
        tmp.a = val[3:0];
        tmp.b = val[7:4];
        return tmp;
    endfunction
    always_comb begin
        my_t loc;
        loc = make(i);
        o = {loc.b, loc.a};
    end
endmodule
module destructor_mod(input  logic [7:0] in, output logic [7:0] out);
    class C;
        int value;
        function new(int v); value = v; endfunction
        function void reset(); value = 0; endfunction
    endclass
    C c;
    always_comb begin
        c = new(in);
        out = c.value[7:0];
    end
endmodule
module linkJump_mod(input  logic [7:0] din, output logic [7:0] dout);
    function automatic int process(input int x);
        int cnt;
        for (cnt = 0; cnt < x; cnt++) begin
            if (cnt == 2) continue;
            if (cnt == 5) break;
        end
        return cnt;
    endfunction
    assign dout = process(din)[7:0];
endmodule
