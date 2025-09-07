module wildmatchi_module(
    input string s,
    input string p,
    output logic match
);
    always_comb begin
        match = 0;
        automatic int si = 0, pi = 0;
        automatic string ss = s, pp = p;
        match = (ss == pp);
        if (pp.len() > 0 && pp[0] == "*") match = 1;
    end
endmodule
module wildmatch_module(
    input string s,
    input string p,
    output logic match
);
    always_comb begin
        match = (s == p) || (p == "*");
    end
endmodule
module dot_module(
    input string a,
    input string d,
    input string b,
    output string out
);
    always_comb begin
        if (b.len() == 0) out = a;
        else if (a.len() == 0) out = b;
        else out = {a, d, b};
    end
endmodule
module downcase_module(
    input string in,
    output string out
);
    always_comb begin
        out = "";
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (c >= "A" && c <= "Z") out = {out, byte'(c + 8'h20)};
            else out = {out, c};
        end
    end
endmodule
module upcase_module(
    input string in,
    output string out
);
    always_comb begin
        out = "";
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (c >= "a" && c <= "z") out = {out, byte'(c - 8'h20)};
            else out = {out, c};
        end
    end
endmodule
module quoteAny_module(
    input string in,
    input byte tgt,
    input byte esc,
    output string out
);
    always_comb begin
        out = "";
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (c == tgt) out = {out, esc};
            out = {out, c};
        end
    end
endmodule
module dequotePercent_module(
    input string in,
    output string out
);
    always_comb begin
        out = "";
        byte last = 0;
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (last == "%" && c == "%") begin
                last = 0;
            end else begin
                out = {out, c};
                last = c;
            end
        end
    end
endmodule
module quoteStringLiteral_module(
    input string in,
    output string out
);
    always_comb begin
        byte dquote = "\"";
        byte esc = "\\";
        out = {dquote, esc, dquote};
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (c == dquote || c == esc) out = {out, esc};
            out = {out, c};
        end
        out = {out, esc, dquote, dquote};
    end
endmodule
module escapePath_module(
    input string in,
    output string out
);
    always_comb begin
        out = "";
        if (in.find("\\\\") != -1 || in.find("/") != -1) begin
            out = in;
        end else begin
            byte sp = " ";
            byte esc = "\\";
            for (int i = 0; i < in.len(); i++) begin
                byte c = in[i];
                if (c == sp || c == esc) out = {out, esc};
                out = {out, c};
            end
        end
    end
endmodule
module unquoteSV_module(
    input string in,
    output string out,
    output string err
);
    always_comb begin
        err = "";
        out = "";
        bit quoted = 0;
        byte oct = 0;
        int od = 0;
        for (int idx = 0; idx < in.len(); idx++) begin
            byte c = in[idx];
            if (quoted) begin
                if (c >= "0" && c <= "7") begin
                    oct = oct * 8 + (c - "0");
                    od++;
                    if (od == 3) begin
                        out = {out, oct};
                        od = 0; oct = 0;
                        quoted = 0;
                    end
                end else begin
                    if (od) begin
                        out = {out, oct};
                        od = 0; oct = 0;
                        quoted = 0;
                        idx--; continue;
                    end
                    quoted = 0;
                    case (c)
                        "n": out = {out, "\n"};
                        "r": out = {out, "\r"};
                        "t": out = {out, "\t"};
                        "v": out = {out, "\v"};
                        "f": out = {out, "\f"};
                        "a": out = {out, "\a"};
                        default: begin
                            if ((c >= "0" && c <= "9")||(c>="A"&&c<="F")||(c>="a"&&c<="f")) begin
                                err = {"Unknown escape: \\", c};
                                break;
                            end else out = {out, c};
                        end
                    endcase
                end
            end else if (c == "\\") begin
                if (od) begin out = {out, oct}; oct = 0; od = 0; end
                quoted = 1;
            end else begin
                out = {out, c};
            end
        end
    end
endmodule
module removeWhitespace_module(
    input string in,
    output string out
);
    always_comb begin
        out = "";
        for (int i = 0; i < in.len(); i++) begin
            byte c = in[i];
            if (!(c == " " || c=="\t"||c=="\n"||c=="\r")) out = {out, c};
        end
    end
endmodule
module replaceSubstr_module(
    input string in,
    input string frm,
    input string to,
    output string out
);
    always_comb begin
        out = in;
        int pos = out.find(frm);
        while (pos != -1) begin
            out = {out.substr(0,pos), to, out.substr(pos+frm.len())};
            pos = out.find(frm, pos + to.len());
        end
    end
endmodule
module replaceWord_module(
    input string in,
    input string frm,
    input string to,
    output string out
);
    always_comb begin
        out = in;
        int len = frm.len();
        int pos = out.find(frm);
        while (pos != -1) begin
            bit leftid = (pos>0 && (out[pos-1].isalpha()||out[pos-1]=="_"));
            bit rightid = (pos+len<out.len() && (out[pos+len].isalpha()||out[pos+len]=="_"));
            if (!leftid && !rightid)
                out = {out.substr(0,pos), to, out.substr(pos+len)};
            pos = out.find(frm, pos + len);
        end
    end
endmodule
module startsWith_module(
    input string in,
    input string pre,
    output logic match
);
    always_comb begin
        match = (in.len() >= pre.len() && in.substr(0, pre.len()) == pre);
    end
endmodule
module endsWith_module(
    input string in,
    input string suf,
    output logic match
);
    always_comb begin
        match = (in.len() >= suf.len() && in.substr(in.len()-suf.len()) == suf);
    end
endmodule
module murmur_hash_module #(
    parameter WIDTH = 64
) (
    input string in,
    output logic [WIDTH-1:0] hash_out
);
    function automatic [63:0] rotl(input [63:0] x, input int r);
        rotl = (x << r) | (x >> (64-r));
    endfunction
    always_comb begin
        hash_out = 0;
        for (int i = 0; i < in.len(); i += 8) begin
            logic [63:0] k = 0;
            for (int b = 0; b < 8 && i+b<in.len(); b++) begin
                k |= (logic[7:0])in[i+b] << ((7-b)*8);
            end
            hash_out ^= rotl(k * 64'hc6a4a7935bd1e995, 47);
            hash_out *= 64'hc6a4a7935bd1e995;
        end
    end
endmodule
module sha256_block_module(
    input logic [31:0] h_in[8],
    input logic [31:0] chunk[16],
    output logic [31:0] h_out[8]
);
    function automatic [31:0] rotr(input [31:0] x, input int r);
        rotr = (x >> r) | (x << (32-r));
    endfunction
    logic [31:0] w[0:63];
    logic [31:0] ah[0:7];
    always_comb begin
        for (int i = 0; i < 8; i++) ah[i] = h_in[i];
        for (int i = 0; i < 16; i++) w[i] = chunk[i];
        for (int i = 16; i < 64; i++) begin
            w[i] = (rotr(w[i-15],7) ^ rotr(w[i-15],18) ^ (w[i-15]>>3))
                 + w[i-7]
                 + (rotr(w[i-2],17) ^ rotr(w[i-2],19) ^ (w[i-2]>>10))
                 + w[i-16];
        end
        logic [31:0] k[0:63] = '{
            32'h428a2f98,32'h71374491,32'hb5c0fbcf,32'he9b5dba5,
            32'h3956c25b,32'h59f111f1,32'h923f82a4,32'hab1c5ed5,
            32'hd807aa98,32'h12835b01,32'h243185be,32'h550c7dc3,
            32'h72be5d74,32'h80deb1fe,32'h9bdc06a7,32'hc19bf174,
            32'he49b69c1,32'hefbe4786,32'h0fc19dc6,32'h240ca1cc,
            32'h2de92c6f,32'h4a7484aa,32'h5cb0a9dc,32'h76f988da,
            32'h983e5152,32'ha831c66d,32'hb00327c8,32'hbf597fc7,
            32'hc6e00bf3,32'hd5a79147,32'h06ca6351,32'h14292967,
            32'h27b70a85,32'h2e1b2138,32'h4d2c6dfc,32'h53380d13,
            32'h650a7354,32'h766a0abb,32'h81c2c92e,32'h92722c85,
            32'ha2bfe8a1,32'ha81a664b,32'hc24b8b70,32'hc76c51a3,
            32'hd192e819,32'hd6990624,32'hf40e3585,32'h106aa070,
            32'h19a4c116,32'h1e376c08,32'h2748774c,32'h34b0bcb5,
            32'h391c0cb3,32'h4ed8aa4a,32'h5b9cca4f,32'h682e6ff3,
            32'h748f82ee,32'h78a5636f,32'h84c87814,32'h8cc70208,
            32'h90befffa,32'ha4506ceb,32'hbef9a3f7,32'hc67178f2
        };
        logic [31:0] a=ah[0],b=ah[1],c=ah[2],d=ah[3],e=ah[4],f=ah[5],g=ah[6],h=ah[7];
        for (int i = 0; i < 64; i++) begin
            logic [31:0] S1 = rotr(e,6)^rotr(e,11)^rotr(e,25);
            logic [31:0] ch = (e & f) ^ (~e & g);
            logic [31:0] temp1 = h + S1 + ch + k[i] + w[i];
            logic [31:0] S0 = rotr(a,2)^rotr(a,13)^rotr(a,22);
            logic [31:0] maj = (a&b) ^ (a&c) ^ (b&c);
            logic [31:0] temp2 = S0 + maj;
            h = g; g = f; f = e; e = d + temp1;
            d = c; c = b; b = a; a = temp1 + temp2;
        end
        for (int i = 0; i < 8; i++)
            h_out[i] = h_in[i] + (i==0 ? a:(i==1?b:(i==2?c:(i==3?d:(i==4?e:(i==5?f:(i==6?g:h)))))));
    end
endmodule
module VName_dehash_module(
    input string in,
    output string out
);
    always_comb begin
        out = in.replace("__DOT__", ".");
    end
endmodule
module VName_hashed_module(
    input string name,
    input int minL,
    input int maxL,
    output string out
);
    always_comb begin
        if (name.len() < maxL || maxL == 0) out = name;
        else begin
            int pos = name.find("_");
            if (pos < 0) pos = minL;
            out = {name.substr(0,pos), "__hsh"};
        end
    end
endmodule
module editDistance_module(
    input string s,
    input string t,
    output int dist
);
    always_comb begin
        int m = s.len(), n = t.len();
        int d[0:256][0:256];
        for (int i=0;i<=m;i++) d[i][0]=i;
        for (int j=0;j<=n;j++) d[0][j]=j;
        for (int i=1;i<=m;i++)
            for (int j=1;j<=n;j++) begin
                int cost = (s[i-1]==t[j-1])?0:1;
                int del = d[i-1][j]+1;
                int ins = d[i][j-1]+1;
                int sub = d[i-1][j-1]+cost;
                d[i][j] = (del<ins?(del<sub?del:sub):(ins<sub?ins:sub));
                if(i>1&&j>1&&s[i-1]==t[j-2]&&s[i-2]==t[j-1])
                    d[i][j] = d[i][j] < (d[i-2][j-2]+1) ? d[i][j] : d[i-2][j-2]+1;
            end
        dist = d[m][n];
    end
endmodule
module cutoffDistance_module(
    input int glen,
    input int clen,
    output int cut
);
    always_comb begin
        int mx = (glen>clen)?glen:clen;
        int mn = (glen<clen)?glen:clen;
        if (mx <= 1) cut = 0;
        else if (mx-mn <= 1) cut = (mx/3>1?mx/3:1);
        else cut = (mx+2)/3;
    end
endmodule
module bestCandidate_module(
    input string goal,
    input string candidates[$],
    output string best,
    output int dist
);
    always_comb begin
        dist = 1<<30;
        best = "";
        int gLen = goal.len();
        for (int idx = 0; idx < candidates.size(); idx++) begin
            string cand = candidates[idx];
            int cLen = cand.len();
            int mind = (cLen>gLen?cLen-gLen:gLen-cLen);
            if (mind >= dist) continue;
            int cut;
            cutoffDistance_module cd(.glen(gLen), .clen(cLen), .cut(cut));
            cut = cd.cut;
            if (mind > cut) continue;
            editDistance_module ed(.s(goal), .t(cand), .dist(mind));
            if (mind < dist && mind <= cut) begin
                dist = mind;
                best = cand;
            end
        end
        if (dist == 0) best = "";
    end
endmodule
