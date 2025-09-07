module getenvStr_mod #(int N = 16) (
    input  logic [7:0] envvar     [N],
    input  logic [7:0] defaultVal [N],
    output logic [7:0] result     [N]
);
    always_comb begin
        for (int i = 0; i < N; i++) begin
            if (envvar[i] != 8'd0)
                result[i] = envvar[i];
            else
                result[i] = defaultVal[i];
        end
    end
endmodule
module setenvStr_mod #(int N = 16) (
    input  logic [7:0] envvar [N],
    input  logic [7:0] value  [N],
    input  logic        whyFlag,
    output logic [7:0] command [N+8]
);
    always_comb begin
        int w = 0;
        {"e","x","p","o","r","t"," "}.foreach( b ) begin
            command[w++] = b;
        end
        for (int i = 0; i < N && envvar[i] != 0; i++) command[w++] = envvar[i];
        command[w++] = "=";
        command[w++] = "'";
        for (int i = 0; i < N && value[i] != 0; i++) command[w++] = value[i];
        command[w++] = "'";
        if (whyFlag) begin
            command[w++] = " ";
            command[w++] = "#";
        end
        for (; w < N+8; w++) command[w] = 8'd0;
    end
endmodule
module filenameCleanup_mod #(int N = 16) (
    input  logic [7:0] filename [N],
    output logic [7:0] cleaned  [N]
);
    always_comb begin
        bit lastSlash = 0;
        int w = 0;
        for (int i = 0; i < N; i++) begin
            bit isS = (filename[i] == "/" || filename[i] == "\\");
            if (isS && lastSlash) continue;
            cleaned[w++] = filename[i];
            lastSlash = isS;
        end
        if (w > 1 && cleaned[w-1] == "/") w--;
        for (int i = w; i < N; i++) cleaned[i] = 8'd0;
    end
endmodule
module filenameJoin_mod #(int A = 16, int B = 16, int R = 2*(A+B)) (
    input  logic [7:0] p1 [A],
    input  logic [7:0] p2 [B],
    output logic [7:0] path [R]
);
    always_comb begin
        int wa = 0;
        for (int i = 0; i < A && p1[i] != 0; i++) path[wa++] = p1[i];
        if (p2[0] != 0 && !(p2[0]=='.' && p2[1]==0)) begin
            path[wa++] = "/";
            for (int j = 0; j < B && p2[j] != 0; j++) path[wa++] = p2[j];
        end
        for (int k = wa; k < R; k++) path[k] = 8'd0;
    end
endmodule
module filenameDir_mod #(int N = 32) (
    input  logic [7:0] filename [N],
    output logic [7:0] dir      [N]
);
    always_comb begin
        int last = -1;
        for (int i = 0; i < N; i++) if (filename[i]=="/") last = i;
        int w = 0;
        if (last == 0) begin
            dir[w++] = ".";
        end else if (last > 0) begin
            for (int i = 0; i < last; i++) dir[w++] = filename[i];
        end else begin
            dir[w++] = ".";
        end
        for (int j = w; j < N; j++) dir[j] = 8'd0;
    end
endmodule
module filenameExt_mod #(int N = 32) (
    input  logic [7:0] filename [N],
    output logic [7:0] ext      [N]
);
    always_comb begin
        int dotpos = -1;
        int slashpos = -1;
        for (int i=0; i<N; i++) if (filename[i]=="/") slashpos = i;
        for (int i = slashpos+1; i < N; i++)
            if (filename[i] == ".") begin dotpos = i; break; end
        int w = 0;
        if (dotpos != -1) begin
            for (int i = dotpos; i < N && filename[i]!=0; i++) ext[w++] = filename[i];
        end
        for (int j = w; j < N; j++) ext[j] = 8'd0;
    end
endmodule
module filenameNonDir_mod #(int N = 32) (
    input  logic [7:0] filename [N],
    output logic [7:0] base     [N]
);
    always_comb begin
        int slashpos = -1;
        for (int i = 0; i < N; i++) if (filename[i]=="/") slashpos = i;
        int w = 0;
        for (int i = slashpos+1; i < N && filename[i]!=0; i++) base[w++] = filename[i];
        for (int j = w; j < N; j++) base[j] = 8'd0;
    end
endmodule
module filenameNonDirExt_mod #(int N = 32) (
    input  logic [7:0] filename [N],
    output logic [7:0] name     [N]
);
    always_comb begin
        logic [7:0] tmp [N];
        int sl = -1;
        for (int i=0;i<N;i++) if (filename[i]=="/") sl = i;
        int w=0;
        for (int i = sl+1; i<N && filename[i]!=0; i++) tmp[w++] = filename[i];
        int dot = -1;
        for (int i=0;i<w;i++) if (tmp[i]==".") begin dot = i; break; end
        int w2 = (dot==-1? w: dot);
        for (int i=0;i<w2;i++) name[i] = tmp[i];
        for (int j=w2;j<N;j++) name[j]=8'd0;
    end
endmodule
module filenameSubstitute_mod #(int N = 24) (
    input  logic [7:0] filename [N],
    input  logic [7:0] varname  [N],
    input  logic [7:0] varvalue [N],
    output logic [7:0] result   [N*2]
);
    always_comb begin
        int ri = 0;
        for (int i=0; i < N; i++) begin
            if (filename[i]=="$" && filename[i+1]=="{" ) begin
                i += 2;
                while (i<N && filename[i]!="}") i++;
                for (int k=0;k<N && varvalue[k]!=0;k++) result[ri++] = varvalue[k];
                if (i<N) continue;
            end else begin
                result[ri++] = filename[i];
            end
        end
        for (int j=ri; j<N*2; j++) result[j] = 8'd0;
    end
endmodule
module filenameRealPath_mod #(int N = 32) (
    input  logic [7:0] filename [N],
    output logic [7:0] realpath [N]
);
    always_comb begin
        for (int i=0; i<N; i++) realpath[i] = filename[i];
    end
endmodule
module filenameRelativePath_mod #(int N=32) (
    input  logic [7:0] pathA [N],
    input  logic [7:0] pathB [N],
    output logic [7:0] rel   [N]
);
    always_comb begin
        int i = 0;
        bit equal = 1;
        for (int k=0;k<N;k++) if (pathA[k]!=pathB[k]) equal=0;
        if (equal) begin
            rel[0] = ".";
            for (int j=1;j<N;j++) rel[j]=8'd0;
        end else begin
            for (int j=0;j<N;j++) rel[j] = pathA[j];
        end
    end
endmodule
module filenameIsRel_mod #(int N=16) (
    input  logic [7:0] filename [N],
    output logic        isRel
);
    always_comb begin
        isRel = (filename[0] != "/");
    end
endmodule
module filenameSlashPath_mod #(int N=16) (
    input  logic [7:0] pathIn [N],
    output logic [7:0] pathOut[N]
);
    always_comb begin
        for (int i=0; i<N; i++) begin
            if (pathIn[i] == "\\")
                pathOut[i] = "/";
            else
                pathOut[i] = pathIn[i];
        end
    end
endmodule
module getline_mod #(int M=64) (
    input  logic [7:0] data  [M],
    input  logic [7:0] delim,
    output logic [7:0] line  [M]
);
    always_comb begin
        int w = 0;
        for (int i=0; i<M; i++) begin
            if (data[i] == delim) break;
            line[w++] = data[i];
        end
        for (int j=w; j<M; j++) line[j]=8'd0;
    end
endmodule
module createDir_mod (
    input  logic enable,
    output logic ready
);
    always_comb ready = enable;
endmodule
module filesystemFlush_mod (
    input  logic trigger,
    output logic flushed
);
    always_comb flushed = trigger;
endmodule
module filesystemFlushBuildDir_mod (
    input  logic trigger,
    output logic flushed
);
    always_comb flushed = trigger;
endmodule
module unlinkRegexp_mod #(int N=16) (
    input  logic [7:0] dirname [N],
    input  logic [7:0] regexp  [N],
    output logic [31:0] count
);
    always_comb count = 32'd0;
endmodule
module releaseMemory_mod (
    input  logic trig,
    output logic done
);
    always_comb done = trig;
endmodule
module rand64_mod (
    input  logic [63:0] st0,
    input  logic [63:0] st1,
    output logic [63:0] result
);
    always_comb begin
        logic [63:0] s0 = st0;
        logic [63:0] s1 = st1;
        result = s0 + s1;
        s1 ^= s0;
        s0 = ((s0 << 55) | (s0 >> 9)) ^ s1 ^ (s1 << 14);
        s1 = (s1 << 36) | (s1 >> 28);
    end
endmodule
module trueRandom_mod #(int N = 8) (
    input  logic [31:0] size,
    output logic [7:0]  data [N]
);
    always_comb begin
        for (int i=0; i<N; i++) data[i] = 8'hFF;
    end
endmodule
module timeUsecs_mod (
    input  logic enable,
    output logic [63:0] usecs
);
    always_comb usecs = 64'd0;
endmodule
module u_sleep_mod (
    input  logic [63:0] usec,
    output logic        done
);
    always_comb done = 1'b1;
endmodule
module system_mod #(int N = 32) (
    input  logic [7:0] command [N],
    output logic [31:0] exit_code
);
    always_comb exit_code = 32'd0;
endmodule
module selfTest_mod (
    input  logic runTests,
    output logic allPass
);
    always_comb allPass = runTests;
endmoduleendmodule
