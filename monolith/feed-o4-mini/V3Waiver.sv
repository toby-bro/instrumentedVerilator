module find_newline(
    input string in_str,
    output int pos
);
class Dummy; endclass
always_comb begin
    static Dummy d = new();
    pos = in_str.len();
    for (int i = 0; i < in_str.len(); i++) begin
        if (in_str.getc(i) == 8'h0A) begin
            pos = i;
            break;
        end
    end
end
endmodule
module trim_message(
    input bit multiline,
    input string msg,
    output string out
);
class Trimmer; endclass
always_comb begin
    static Trimmer t = new();
    int pos;
    string s;
    if (!multiline) begin
        pos = msg.len();
        for (int i = 0; i < msg.len(); i++) begin
            if (msg.getc(i) == 8'h0A) begin
                pos = i;
                break;
            end
        end
        s = msg.substr(0, pos);
        if (pos != msg.len()) s = {s, "*"};
        out = s;
    end else begin
        out = {msg, "*"};
    end
end
endmodule
module remove_context(
    input string in_str,
    output string out
);
class ContextRemover; endclass
always_comb begin
    static ContextRemover cr = new();
    int cp;
    string result;
    cp = 0;
    result = "";
    while (cp < in_str.len()) begin
        byte c;
        c = in_str.getc(cp);
        if (((c >= 8'h30) && (c <= 8'h39)) || (c == 8'h20)) begin
            cp = cp + 1;
        end else if (c == 8'h7C) begin
            cp = cp + 1;
        end else begin
            while ((cp < in_str.len()) && ((in_str.getc(cp) == 8'h20) || (in_str.getc(cp) == 8'h5E))) cp = cp + 1;
            while ((cp < in_str.len()) && (in_str.getc(cp) == 8'h7E)) cp = cp + 1;
            while ((cp < in_str.len()) && (in_str.getc(cp) != 8'h0A)) begin
                result[result.len()] = in_str.getc(cp);
                cp = cp + 1;
            end
            while ((cp < in_str.len()) && (in_str.getc(cp) == 8'h0A)) begin
                result[result.len()] = in_str.getc(cp);
                cp = cp + 1;
            end
        end
    end
    out = result;
end
endmodule
module compress_asterisk(
    input string in_str,
    output string out
);
class Compressor; endclass
always_comb begin
    static Compressor c = new();
    string result;
    string add;
    result = "";
    add = "";
    for (int i = 0; i < in_str.len(); i++) begin
        byte ch;
        ch = in_str.getc(i);
        if ((ch == 8'h2A) || (ch < 8'h20) || (ch > 8'h7E)) begin
            add = "*";
        end else if (ch == 8'h20) begin
            if (add != "*") add = {add, " "};
        end else begin
            result = {result, add};
            result[result.len()] = ch;
            add = "";
        end
    end
    result = {result, add};
    out = result;
end
endmodule
module entry_builder(
    input string errorCode,
    input string filename,
    input string match_str,
    output string entry
);
class EntryBuilder; endclass
always_comb begin
    static EntryBuilder eb = new();
    entry = {"lint_off -rule ", errorCode,
             " -file \"*", filename,
             "\" -match \"", match_str, "\""};
end
endmodule
module write_config #(
    parameter int N = 4
)(
    input bit has_waivers,
    input int count,
    input string waivers [0:N-1],
    output string file_out
);
class Writer; endclass
always_comb begin
    static Writer w = new();
    file_out = "
    file_out = {file_out, "\140verilator_config\n\n"};
    file_out = {file_out, "
    file_out = {file_out, "
    file_out = {file_out, "
    file_out = {file_out, "
    if (!has_waivers || (count == 0)) begin
        file_out = {file_out, "
    end else begin
        for (int i = 0; i < count && i < N; i++) begin
            file_out = {file_out, "
        end
    end
end
endmodule
