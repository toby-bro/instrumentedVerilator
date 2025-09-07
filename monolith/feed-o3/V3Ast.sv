module arithmetic_mixed(
    input  logic signed [3:0] a,
    input  logic        [5:0] b,
    output logic        [7:0] y
);
    wire signed [7:0] ext_a = $signed(a);
    wire        [7:0] sum   = ext_a + b;
    wire        [7:0] prod  = a * b;
    wire        [7:0] sel   = b[0] ? sum : prod;
    wire        [7:0] concat_val = {a, b[3:0]};
    assign y = sel ^ concat_val;
endmodule
module struct_union_enum_module(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_e;
    typedef struct packed {logic [3:0] hi; logic [3:0] lo;} struct_t;
    typedef union  packed {logic [7:0] raw; struct_t parts;} union_t;
    state_e state;
    union_t u;
    always_comb begin
        u.raw = din;
        state = state_e'(din[1:0]);
        unique case (state)
            S0: dout = u.raw;
            S1: dout = {u.parts.hi, u.parts.lo};
            default: dout = 8'hFF;
        endcase
    end
endmodule
module array_queue_stream(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    typedef logic [7:0] byte_t;
    typedef byte_t byte_q_t[$];
    byte_q_t q;
    byte_t   da[];
    byte_t   packed_arr [3:0];
    always_comb begin
        logic [15:0] repl;
        q = {};
        q.push_back(din);
        da = new[1];
        da[0] = din;
        packed_arr[0] = din;
        if (q.size() != 0)
            dout = q[0];
        else
            dout = 8'h00;
        repl = {2{din}};
        dout = dout ^ repl[7:0];
    end
endmodule
module class_cast_module(
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class base_c;
        virtual function int get(); get = 0; endfunction
    endclass
    class child_c extends base_c;
        int v;
        function new(); v = 5; endfunction
        function int get(); get = v; endfunction
    endclass
    base_c  b;
    child_c c;
    always_comb begin
        int tmp;
        child_c c_from_b;
        if (b == null) b = new();
        if (c == null) c = new();
        tmp = c.get() + in_val;
        if ($cast(c_from_b, b))
            tmp = tmp + c_from_b.get();
        out_val = tmp[3:0];
    end
endmodule
module function_width_module(
    input  logic [15:0] in_w,
    output logic [15:0] out_w
);
    function automatic int compute(input int x);
        int acc;
        acc = 0;
        for (int i = 0; i < 4; i++) begin
            acc += (x >> i);
        end
        return acc;
    endfunction
    localparam signed [31:0] CONST = -32'sd5;
    wire signed [31:0] resized = $signed({{16{in_w[15]}}, in_w}) + CONST;
    assign out_w = compute(resized)[15:0];
endmodule
