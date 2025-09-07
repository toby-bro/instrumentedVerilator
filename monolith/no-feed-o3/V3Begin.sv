module begin_named_foreach #(parameter W = 8, parameter DEP1 = 4, parameter DEP2 = 4)
    (input  logic clk,
     input  logic rst,
     output logic [W-1:0] out);
    logic [W-1:0] mem [0:DEP1-1][0:DEP2-1];
    always_ff @(posedge clk or posedge rst) begin : MAIN_BEGIN
        if (rst) begin : RESET_BLOCK
            foreach (mem[i, j]) begin
                mem[i][j] <= '0;
            end
            out <= '0;
        end else begin : RUN_BLOCK
            automatic int sum;
            function automatic int add_val (input int a, input int b);
                static int cnt = 0;
                cnt = cnt + 1;
                add_val = a + b;
            endfunction
            sum = 0;
            foreach (mem[ii, jj]) begin : SUM_LOOP
                sum = add_val(sum, mem[ii][jj]);
            end
            fork : PARALLEL_CALC
                begin
                    out <= sum[W-1:0];
                end
            join_none
        end
    end
endmodule
class Obj;
    int v;
    function new (int x); v = x; endfunction
endclass
module dynamic_array_mod (input  logic clk,
                          output logic done);
    int    dyn[];
    int    q[$];
    string str;
    always_ff @(posedge clk) begin : PROC
        if (dyn.size() == 0) begin
            dyn = new[5];
            for (int idx = 0; idx < dyn.size(); idx++) begin
                dyn[idx] = idx;
            end
        end
        if (q.size() == 0) begin
            q.push_back(1);
            q.push_back(2);
            q.push_back(3);
        end
        if (str.len() == 0) begin
            str = "test";
        end
        automatic Obj o;
        o = new(5);
        int sum = 0;
        foreach (dyn[i])  sum += dyn[i];
        foreach (q[j])    sum += q[j];
        foreach (str[k])  sum += str[k];
        unique if (dyn.size() == 0) begin
            done <= 0;
        end else begin
            if (sum > 4) begin
                if (sum > 8) begin
                    if (sum > 12) begin
                        if (sum > 16) begin
                            if (sum > 20) begin
                                done <= 1;
                            end
                        end
                    end
                end
            end
        end
    end
endmodule
module typedef_generate_mod #(parameter WIDTH = 8)
    (input  logic              sel,
     output logic [WIDTH-1:0]  out);
    begin : TYPE_BEGIN
        typedef struct packed {
            logic [WIDTH-1:0] a;
            logic [WIDTH-1:0] b;
        } pair_t;
        pair_t p;
        always_comb begin : COMB
            p.a = sel ? {WIDTH{1'b1}} : '0;
            p.b = ~p.a;
            out = p.a & p.b;
        end
    end
endmodule
module child_mod (input  logic in,
                  output logic out);
    always_comb out = in;
endmodule
module parent_mod (input  logic in,
                   output logic out);
    logic out_child;
    child_mod u_child (.in(in), .out(out_child));
    assign out = out_child;
    generate
        begin : GEN_PARENT
            logic dummy;
            always_comb dummy = in & out_child;
        end
    endgenerate
endmodule
