module mod_const_pool #(parameter WIDTH = 512) (input logic [WIDTH-1:0] in, output logic [WIDTH-1:0] out);
    localparam logic [WIDTH-1:0] CONST_LARGE = 'hDEADBEEFDEADBEEFDEADBEEFDEADBEEF;
    assign out = in ^ CONST_LARGE;
endmodule
module mod_shift_ops (input logic [31:0] a, input logic [4:0] sh, output logic [31:0] lsl, output logic [31:0] lsr, output logic signed [31:0] asr);
    assign lsl = a << sh;
    assign lsr = a >> sh;
    assign asr = $signed(a) >>> sh;
endmodule
module mod_while_loop (input logic enable, input logic [7:0] start, output logic [7:0] result);
    always_comb begin
        logic [7:0] tmp;
        tmp = start;
        while (tmp != 0) begin
            tmp = tmp - 1;
            if (enable)
                tmp = tmp - 1;
        end
        result = tmp;
    end
endmodule
module mod_complex_assign (input logic [3:0] a, input logic [3:0] b, output logic [4:0] sum, output logic [3:0] bitwise);
    assign sum = a + b;
    assign bitwise = (~a & b) | (a ^ b);
endmodule
module mod_term_uniop (input logic [3:0] a, output logic [3:0] neg, output logic norred);
    assign neg = -a;
    assign norred = !(|a);
endmodule
module mod_array_packed (input logic [7:0] arr [0:3], input int idx, output logic [31:0] packed_out, output logic [7:0] unpacked_out [0:3]);
    logic [31:0] tmp;
    always_comb begin
        tmp = {arr[3], arr[2], arr[1], arr[0]};
        for (int i = 0; i < 4; i = i + 1)
            unpacked_out[i] = tmp[i*8 +: 8];
    end
    assign packed_out = tmp;
endmodule
module mod_unpacked_queue (input logic push, input logic pop, input logic [7:0] din, output logic [7:0] dout);
    logic [7:0] q[$];
    always_comb begin
        if (push)
            q.push_back(din);
        if (pop && q.size())
            q.pop_front();
        dout = (q.size() ? q[0] : '0);
    end
endmodule
module mod_assoc_sel (input string key, input int val, output int out);
    int mem[string];
    always_comb begin
        mem[key] = val;
        out = mem[key];
    end
endmodule
module mod_sel (input logic [15:0] data, input int index, output logic bit_out, output logic [3:0] slice_out);
    assign bit_out = data[index];
    assign slice_out = data[index +: 4];
endmodule
module mod_cond (input logic cond, input logic [7:0] a, input logic [7:0] b, output logic [7:0] out);
    assign out = cond ? a : b;
endmodule
module mod_sformat (input logic [7:0] a, output string s);
    function string fmt(input logic [7:0] v);
        string tmp;
        tmp = $sformatf("Value: %0d", v);
        return tmp;
    endfunction
    assign s = fmt(a);
endmodule
module mod_rand (input logic [7:0] seed, output logic [7:0] rnd);
    function logic [7:0] gen(input logic [7:0] sd);
        gen = $urandom(sd);
    endfunction
    assign rnd = gen(seed);
endmodule
module mod_ucfunc (input logic a, input logic b, output logic y);
    function logic foo(input logic x);
        foo = ~x;
    endfunction
    assign y = foo(a) & foo(b);
endmodule
