module GraphRemoveRedundant_mod #(parameter int N = 8) (
    input  logic              clk,
    input  logic              enable,
    input  logic [31:0]       in_data [N],
    output logic [31:0]       out_data [N]
);
    class Remover;
        bit sumWeights;
        function new(bit sumW);
            sumWeights = sumW;
        endfunction
        function void process(input logic [31:0] in_arr [N], ref logic [31:0] out_arr [N]);
            int i;
            for (i = 0; i < N; i = i + 1) out_arr[i] = 0;
            for (i = 0; i < N; i = i + 1) begin
                logic [31:0] val = in_arr[i];
                if (out_arr[i] == 0) out_arr[i] = val;
                else if (sumWeights) out_arr[i] = out_arr[i] + val;
                else out_arr[i] = (out_arr[i] > val) ? out_arr[i] : val;
            end
        endfunction
    endclass
    Remover rem;
    always_ff @(posedge clk) begin
        if (enable) begin
            rem = new(1);
            rem.process(in_data, out_data);
        end
    end
endmodule
module GraphRemoveTransitive_mod #(parameter int N = 8) (
    input  logic        clk,
    input  logic        go,
    input  int          in_list [N],
    output int          out_list [N]
);
    class Transitive;
        int outQueue[$];
        function new();
            outQueue.delete();
        endfunction
        function void goProc(input int inArr [N]);
            int i;
            outQueue.delete();
            for (i = 0; i < N; i = i + 1)
                if ((inArr[i] & 1) == 0)
                    outQueue.push_back(inArr[i]);
        endfunction
        function void writeOutput(ref int outArr [N]);
            int i;
            for (i = 0; i < N; i = i + 1)
                if (i < outQueue.size()) outArr[i] = outQueue[i];
                else outArr[i] = 0;
        endfunction
    endclass
    Transitive tr;
    always_ff @(posedge clk) begin
        if (go) begin
            tr = new();
            tr.goProc(in_list);
            tr.writeOutput(out_list);
        end
    end
endmodule
module GraphWeakly_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        start,
    input  bit          adj     [V][V],
    output int          color   [V]
);
    class Weakly;
        bit visited [V];
        int cols    [V];
        function new();
        endfunction
        function void run(input bit adj_in [V][V]);
            int i;
            int curr;
            for (i = 0; i < V; i = i + 1) begin visited[i] = 0; cols[i] = 0; end
            curr = 0;
            for (i = 0; i < V; i = i + 1)
                if (!visited[i]) begin curr = curr + 1; dfs(i, curr, adj_in); end
        endfunction
        function void dfs(int v, int c, input bit adj_in [V][V]);
            int u;
            if (visited[v]) return;
            visited[v] = 1;
            cols[v]    = c;
            for (u = 0; u < V; u = u + 1)
                if (adj_in[v][u]) dfs(u, c, adj_in);
        endfunction
    endclass
    Weakly wk;
    always_ff @(posedge clk) begin
        if (start) begin
            wk = new();
            wk.run(adj);
            for (int i = 0; i < V; i = i + 1) color[i] = wk.cols[i];
        end
    end
endmodule
module GraphStrongly_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        start,
    input  bit          adj     [V][V],
    output int          comp_id [V]
);
    class Strongly;
        int usera     [V];
        int cola      [V];
        int callTrace [$];
        int dfsCnt;
        function new();
        endfunction
        function void run(input bit adj_in [V][V]);
            int i;
            dfsCnt = 1;
            for (i = 0; i < V; i = i + 1) begin usera[i] = 0; cola[i] = 0; end
            for (i = 0; i < V; i = i + 1)
                if (usera[i] == 0) iterate(i, adj_in);
            for (i = 0; i < V; i = i + 1) begin
                bit onecol = 1;
                for (int j = 0; j < V; j = j + 1)
                    if (adj_in[i][j] && (cola[i] == cola[j])) onecol = 0;
                if (onecol) cola[i] = 0;
            end
        endfunction
        function void iterate(int v, input bit adj_in [V][V]);
            int u;
            int thisDfs = dfsCnt;
            dfsCnt = dfsCnt + 1;
            usera[v] = thisDfs;
            cola[v]  = 0;
            for (u = 0; u < V; u = u + 1)
                if (adj_in[v][u]) begin
                    if (usera[u] == 0) iterate(u, adj_in);
                    if ((cola[u] == 0) && (usera[v] > usera[u])) usera[v] = usera[u];
                end
            if (usera[v] == thisDfs) begin
                cola[v] = thisDfs;
                while (callTrace.size() > 0) begin
                    int w = callTrace[callTrace.size()-1];
                    if (usera[w] >= thisDfs) begin callTrace.pop_back(); cola[w] = thisDfs; end
                    else break;
                end
            end else callTrace.push_back(v);
        endfunction
    endclass
    Strongly sg;
    always_ff @(posedge clk) begin
        if (start) begin
            sg = new();
            sg.run(adj);
            for (int i = 0; i < V; i = i + 1) comp_id[i] = sg.cola[i];
        end
    end
endmodule
module GraphRank_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        start,
    input  bit          adj      [V][V],
    output int          rank_out [V]
);
    class Ranker;
        int usera [V];
        int ranxa [V];
        function new();
        endfunction
        function void run(input bit adj_in [V][V]);
            for (int i = 0; i < V; i = i + 1) begin usera[i] = 0; ranxa[i] = 0; end
            for (int i = 0; i < V; i = i + 1)
                if (usera[i] == 0) iterate(i, 1, adj_in);
        endfunction
        function void iterate(int v, int c, input bit adj_in [V][V]);
            if (usera[v] == 1) return;
            if (ranxa[v] >= c) return;
            usera[v] = 1;
            ranxa[v] = c;
            for (int u = 0; u < V; u = u + 1)
                if (adj_in[v][u]) iterate(u, c + 1, adj_in);
            usera[v] = 2;
        endfunction
    endclass
    Ranker rk;
    always_ff @(posedge clk) begin
        if (start) begin
            rk = new();
            rk.run(adj);
            for (int i = 0; i < V; i = i + 1) rank_out[i] = rk.ranxa[i];
        end
    end
endmodule
module GraphLoops_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        start,
    input  bit          adj      [V][V],
    input  int          seed,
    output string       msg_out
);
    class RLoops;
        int usera      [V];
        int callTrace  [$];
        string msgs    [$];
        bit done;
        function new();
        endfunction
        function void run(int entry, input bit adj_in [V][V]);
            for (int i = 0; i < V; i = i + 1) usera[i] = 0;
            done = 0;
            callTrace.delete();
            msgs.delete();
            iterate(entry, 0, adj_in);
        endfunction
        function void iterate(int v, int depth, input bit adj_in [V][V]);
            int u;
            if (done) return;
            while (callTrace.size() <= depth) callTrace.push_back(0);
            callTrace[depth] = v;
            if (usera[v] == 1) begin
                for (int k = 0; k <= depth; k = k + 1) msgs.push_back($sformatf("Loop%0d", callTrace[k]));
                done = 1;
                return;
            end
            if (usera[v] == 2) return;
            usera[v] = 1;
            for (u = 0; u < V; u = u + 1)
                if (adj_in[v][u]) iterate(u, depth + 1, adj_in);
            usera[v] = 2;
        endfunction
        function string get_msg();
            string s = "";
            for (int i = 0; i < msgs.size(); i = i + 1) s = {s, msgs[i], ";"};
            return s;
        endfunction
    endclass
    RLoops rl;
    always_ff @(posedge clk) begin
        if (start) begin
            rl = new();
            rl.run(seed % V, adj);
            msg_out = rl.get_msg();
        end
    end
endmodule
module GraphSubtrees_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        start,
    input  bit          adj            [V][V],
    output bit          copy_adj_flat [(V*V)]
);
    class Subtrees;
        bit visited    [V];
        bit clone_adj  [V][V];
        function new();
        endfunction
        function void run(input bit adj_in [V][V]);
            for (int i = 0; i < V; i = i + 1) visited[i] = 0;
            for (int i = 0; i < V; i = i + 1)
                for (int j = 0; j < V; j = j + 1) clone_adj[i][j] = 0;
            clone_all(0, adj_in);
        endfunction
        function void clone_all(int v, input bit adj_in [V][V]);
            if (visited[v]) return;
            visited[v] = 1;
            for (int u = 0; u < V; u = u + 1)
                if (adj_in[v][u]) begin clone_adj[v][u] = 1; clone_all(u, adj_in); end
        endfunction
    endclass
    Subtrees st;
    always_ff @(posedge clk) begin
        if (start) begin
            st = new();
            st.run(adj);
            for (int i = 0; i < V; i = i + 1)
                for (int j = 0; j < V; j = j + 1)
                    copy_adj_flat[i*V + j] = st.clone_adj[i][j];
        end
    end
endmodule
module GraphSort_mod #(parameter int M = 16) (
    input  logic        clk,
    input  logic        sort_en,
    input  int          arr_in  [M],
    output int          arr_out [M]
);
    function bit cmp(int a, int b);
        return a < b;
    endfunction
    always_ff @(posedge clk) begin
        if (sort_en) begin
            int buff [M];
            int i, j, key, k;
            for (i = 0; i < M; i = i + 1) buff[i] = arr_in[i];
            for (i = 1; i < M; i = i + 1) begin
                key = buff[i];
                j   = i - 1;
                while ((j >= 0) && (!cmp(buff[j], key))) begin
                    buff[j+1] = buff[j];
                    j = j - 1;
                end
                buff[j+1] = key;
            end
            for (k = 0; k < M; k = k + 1) arr_out[k] = buff[k];
        end
    end
endmodule
module GraphParallelism_mod #(parameter int V = 8) (
    input  logic        clk,
    input  logic        run,
    input  int          cost        [V],
    input  bit          adj         [V][V],
    output longint      vertexCount,
    output longint      edgeCount,
    output longint      totalCost,
    output longint      criticalPath
);
    class ParallelismReport;
        typedef longint lu;
        lu vCount;
        lu eCount;
        lu tCost;
        lu cPath;
        lu critPaths [V];
        function new();
            for (int i = 0; i < V; i = i + 1) critPaths[i] = 0;
            vCount = 0;
            eCount = 0;
            tCost  = 0;
            cPath  = 0;
        endfunction
        function void run(input int cost_in [V], input bit adj_in [V][V]);
            int idx;
            int node;
            int order_queue[$];
            order_queue.delete();
            for (int i = 0; i < V; i = i + 1) order_queue.push_back(i);
            for (idx = 0; idx < order_queue.size(); idx = idx + 1) begin
                lu cp;
                node = order_queue[idx];
                vCount = vCount + 1;
                cp = 0;
                for (int u = 0; u < V; u = u + 1)
                    if (adj_in[node][u]) begin
                        eCount = eCount + 1;
                        cp = (cp > critPaths[u]) ? cp : critPaths[u];
                    end
                cp = cp + cost_in[node];
                critPaths[node] = cp;
                cPath = (cPath > cp) ? cPath : cp;
                tCost = tCost + cost_in[node];
            end
        endfunction
    endclass
    ParallelismReport pr;
    always_ff @(posedge clk) begin
        if (run) begin
            pr = new();
            pr.run(cost, adj);
            vertexCount  = pr.vCount;
            edgeCount    = pr.eCount;
            totalCost    = pr.tCost;
            criticalPath = pr.cPath;
        end
    end
endmodule
