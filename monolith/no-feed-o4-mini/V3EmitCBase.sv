module EmCPar (input  logic        clk,
                input  logic [7:0]  data_in,
                output logic [7:0]  data_out);
    parameter int SIZE = 8;
    logic [7:0] arr[SIZE];
    always_ff @(posedge clk) begin
        for (int i = 0; i < SIZE; i = i + 1)
            arr[i] <= data_in + i;
    end
    assign data_out = arr[SIZE-1];
endmodule
module PrefixNameProtect (input  logic [7:0] char_in,
                          input  logic       flag,
                          output logic [7:0] char_out);
    function automatic byte prefix_protect(byte c, bit f);
        static byte memo[256];
        byte res;
        if (memo[c] != 8'h00) begin
            res = memo[c];
        end else begin
            res = c ^ (f ? 8'hAA : 8'h55);
            memo[c] = res;
        end
        return res;
    endfunction
    assign char_out = prefix_protect(char_in, flag);
endmodule
module FuncNameProtect (input  logic ctor,
                        input  logic dtor,
                        output logic [3:0] name_len);
    typedef enum logic [1:0] { NONE=2'd0, LOOSE=2'd1 } mode_t;
    function automatic int protect_len(mode_t m, string name);
        if (ctor)
            return name.len();
        else if (dtor)
            return name.len() + 1;
        else if (m == LOOSE)
            return name.len() + 2;
        else
            return name.len();
    endfunction
    string nm = "module";
    assign name_len = protect_len(ctor ? NONE : LOOSE, nm);
endmodule
module NewCFileCreate (input  logic slow,
                       input  logic src,
                       output logic ok);
    class CFile;
        bit slowFlag;
        bit srcFlag;
        function new(bit s, bit t);
            slowFlag = s;
            srcFlag  = t;
        endfunction
    endclass
    CFile cf;
    always_comb begin
        cf = new(slow, src);
        ok = cf.slowFlag & cf.srcFlag;
    end
endmodule
module CFuncArgsMod (input  logic loose,
                     input  logic isConst,
                     input  logic needProc,
                     output logic [31:0] arg_count);
    function automatic int build_args(bit loose, bit cst, bit proc);
        int count = 0;
        if (loose && !cst)
            count++;
        if (proc)
            count++;
        byte types[] = '{8, 16, 32};
        foreach (types[i])
            count += types[i] / 8;
        return count;
    endfunction
    assign arg_count = build_args(loose, isConst, needProc);
endmodule
module EmitCFuncHeaderDecl (input  logic isStatic,
                             input  logic isVirtual,
                             output logic [7:0] attr_flags);
    function automatic logic [1:0] getFlags(bit isStat, bit isVirt);
        logic [1:0] flags;
        if (isStat)  flags[0] = 1;
        if (isVirt) flags[1] = 1;
        return flags;
    endfunction
    assign attr_flags = getFlags(isStatic, isVirtual);
endmodule
module EmitVarDeclMod (input  logic isIO,
                       input  logic isSc,
                       input  logic isInout,
                       output logic [3:0] io_type);
    generate
        if (isIO && isSc) begin : name_io
            localparam int TYPE = isInout ? 1 : 0;
            assign io_type = TYPE;
        end else if (isIO && !isSc) begin : vld
            assign io_type = isInout ? 2 : 3;
        end else begin : else_blk
            assign io_type = 0;
        end
    endgenerate
endmodule
module EmitVarAccessorsMod (input  logic [7:0] private_sig,
                            input  logic [7:0] set_val,
                            output logic [7:0] public_sig);
    function automatic logic [7:0] get_val();
        return private_sig;
    endfunction
    function automatic void set_val_fn(logic [7:0] v, output logic [7:0] outv);
        outv = v;
    endfunction
    assign public_sig = get_val();
    always_comb begin
        set_val_fn(set_val, public_sig);
    end
endmodule
module EmitModCUseMod (input  logic useA,
                       input  logic useB,
                       output logic sel);
    wire entries[2];
    assign entries[0] = useA;
    assign entries[1] = useB;
    always_comb begin
        sel = 0;
        for (int i = 0; i < 2; i = i + 1)
            if (entries[i])
                sel = 1;
    end
endmodule
module TextSectionMod (input  logic decorate,
                       input  logic [7:0] code_in,
                       output logic [7:0] code_out);
    function automatic string text_section(input string texts[$], bit decorate);
        string accum = "";
        int last_line = -1;
        foreach (texts[i]) begin
            int lineno = i;
            if (lineno != last_line + 1 && decorate)
                accum = {accum, "//ln", lineno};
            accum = {accum, texts[i]};
            last_line = lineno;
        end
        if (decorate)
            accum = {accum, "//end"};
        return accum;
    endfunction
    string arr[$] = {"abc", "def", "ghi"};
    string result;
    always_comb result = text_section(arr, decorate);
    assign code_out = result.len() ? code_in : 8'hFF;
endmodule
