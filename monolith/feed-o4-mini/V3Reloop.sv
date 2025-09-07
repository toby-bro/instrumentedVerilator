module mod_dumpTreeLevel(input logic [1:0] lvl, output logic [1:0] out);
    always_comb begin
        case(lvl)
            2'd0: out = 2'd0;
            2'd1: out = 2'd1;
            default: out = 2'd3;
        endcase
    end
endmodule
module mod_dumpTreeJsonLevel(input logic [1:0] lvl, output logic [2:0] out);
    function automatic [2:0] json_fn(input logic [1:0] v);
        begin
            json_fn = {1'b1, v};
        end
    endfunction
    assign out = json_fn(lvl);
endmodule
module mod_dumpTreeEitherLevel(input logic [1:0] lvl, output logic out);
    function automatic logic either_fn(input logic [1:0] v);
        begin
            if (v == 2'd2)
                either_fn = 1'b1;
            else
                either_fn = 1'b0;
        end
    endfunction
    assign out = either_fn(lvl);
endmodule
module mod_debug_v(input logic en, input logic [7:0] din, output logic [7:0] dout);
    function automatic [7:0] _debug(input logic [7:0] d);
        begin
            if (en)
                _debug = d;
            else
                _debug = 8'hFF ^ d;
        end
    endfunction
    assign dout = _debug(din);
endmodule
module mod_createVarTemp(input logic [31:0] inc, output logic [31:0] varidx);
    class CVar;
        int idx;
        function new(int init);
            idx = init;
        endfunction
        function void incf();
            idx = idx + 1;
        endfunction
        function int get();
            get = idx;
        endfunction
    endclass
    CVar v;
    always_comb begin
        v = new(inc);
        v.incf();
        varidx = v.get();
    end
endmodule
module mod_mergeEnd_logic(input logic start_merge, input logic [31:0] idx_lo, input logic [31:0] idx_hi, input logic signed [31:0] offset, output logic [31:0] new_lo, output logic [31:0] new_hi);
    parameter int LIMIT = 4;
    logic [31:0] items;
    always_comb begin
        items = idx_hi - idx_lo + 1;
        if (start_merge && items >= LIMIT) begin
            if (offset > 0) begin
                new_lo = idx_lo - offset;
                new_hi = idx_hi - offset;
            end else begin
                new_lo = idx_lo;
                new_hi = idx_hi;
            end
        end else begin
            new_lo = idx_lo;
            new_hi = idx_hi;
        end
    end
endmodule
module mod_visit_CFunc(input logic [3:0] lvl, input logic trigger, output logic [3:0] nextlvl);
    function automatic [3:0] func(input logic [3:0] l);
        begin
            func = l + 1;
        end
    endfunction
    always_comb begin
        if (trigger)
            nextlvl = func(lvl);
        else
            nextlvl = lvl;
    end
endmodule
module mod_visit_Assign(input logic [31:0] lindex, input logic [31:0] rindex, input logic lhs_sel, input logic rhs_sel, input logic width_gt32, input logic same_var, output logic doMerge);
    always_comb begin
        if (!lhs_sel)
            doMerge = 0;
        else if (width_gt32)
            doMerge = 0;
        else if (!rhs_sel)
            doMerge = 1;
        else if (same_var)
            doMerge = 0;
        else
            doMerge = (lindex == rindex);
    end
endmodule
module mod_visit_ExprStmt(input logic [7:0] a, input logic [7:0] b, output logic [7:0] y);
    always_comb y = a | b;
endmodule
module mod_visit_Var(input logic [7:0] in, output logic [7:0] out);
    always_comb out = in;
endmodule
module mod_visit_NodeExpr(input logic [7:0] a, input logic [7:0] b, output logic [7:0] c);
    function automatic [7:0] expr_fn(input logic [7:0] x, input logic [7:0] y);
        begin
            expr_fn = x ^ y;
        end
    endfunction
    assign c = expr_fn(a, b);
endmodule
module mod_visit_Node(input logic [7:0] in, output logic [7:0] out);
    always_comb begin
        if (in[0])
            out = in;
        else
            out = ~in;
    end
endmodule
module mod_ReloopVisitor_ctor(input logic [7:0] init, input logic [7:0] limit, output logic [31:0] statReloops, output logic [31:0] statReItems);
    int unsigned cntR; int unsigned cntI;
    always_comb begin
        cntR = 0;
        cntI = 0;
        for (int i = 0; i < init; i = i + 1) begin
            cntR += 1;
            cntI += i;
        end
        statReloops = cntR;
        statReItems = cntI;
    end
endmodule
module mod_ReloopVisitor_dtor(input logic [31:0] s1, input logic [31:0] s2, output logic [31:0] tot);
    assign tot = s1 + s2;
endmodule
module mod_reloopAll(input logic go, output logic done);
    logic localDone;
    always_comb begin
        localDone = go;
        done = localDone;
    end
endmodule
module mod_array_generate(input logic [7:0] arr_in [0:7], output logic [7:0] arr_out [0:7]);
    genvar i;
    generate
        for (i = 0; i < 8; i = i + 1) begin : gen_loop
            assign arr_out[i] = arr_in[i] + i;
        end
    endgenerate
endmodule
module mod_while_loop(input logic [7:0] lim, output logic [15:0] sum);
    integer i;
    always_comb begin
        sum = 0;
        i = 0;
        while (i < lim) begin
            sum = sum + i;
            i = i + 1;
        end
    end
endmodule
