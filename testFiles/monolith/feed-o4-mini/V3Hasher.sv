module M1_expr(input logic [7:0] in, output logic [7:0] out);
    logic a_bit;
    wire [3:0] part;
    assign a_bit = in[3];
    assign part = in[7:4];
    wire [7:0] casted;
    assign casted = int'(in) + 'd1;
    assign out = part * casted;
endmodule
module M2_struct(input logic clk, input logic [3:0] in, output logic [3:0] v);
    typedef logic [3:0] nibble_t;
    typedef struct packed { nibble_t hi; nibble_t lo; } myStruct_t;
    typedef union packed { logic [3:0] a; logic [3:0] b; } myUnion_t;
    typedef enum logic [1:0] { IDLE, BUSY, DONE } state_t;
    parameter type T = nibble_t;
    parameter nibble_t lp = 4'b0000;
    myStruct_t s;
    myUnion_t u;
    state_t st;
    always_ff @(posedge clk) begin
        s.hi <= lp;
        s.lo <= in;
        u.b <= {s.hi, s.lo};
        st <= BUSY;
        v <= s.hi;
    end
endmodule
module M3_arrays(input integer idx, output logic val);
    logic [7:0] dyn_arr[];
    logic [3:0] usz_arr[];
    int assoc_arr[string];
    logic queue_arr[$];
    always_comb begin
        if (dyn_arr.size() > 0)
            val = dyn_arr[0];
        else if (assoc_arr.exists("key"))
            val = assoc_arr["key"];
        else if (queue_arr.size() > 0)
            val = queue_arr.pop_front();
        else
            val = 1'b0;
    end
endmodule
module M4_class(input logic clk, output logic done);
    class C;
        int x;
        function int f(input int a);
            return a + x;
        endfunction
    endclass
    C c_obj;
    always_ff @(posedge clk) begin
        c_obj = new;
        c_obj.x = 1;
        done <= c_obj.f(1);
    end
endmodule
module M5_interface(input logic clk, output logic sig);
    interface I (input logic clk_i);
        logic bar;
        modport MP (input bar);
    endinterface
    I i_if(.clk_i(clk));
    always_comb begin
        sig = i_if.bar;
    end
endmodule
module M6_generate(input logic en, input logic [3:0] in, output logic [3:0] out);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_loop
            assign out[i] = en ? in[i] : ~in[i];
        end
    endgenerate
endmodule
module M7_assert(input logic clk, input logic [3:0] in, output logic ok);
    property p_chk;
        @(posedge clk) disable iff (1'b0) in != 4'hF;
    endproperty
    assert property (p_chk);
    assign ok = in != 4'hF;
endmodule
module M8_param_type(input logic [7:0] in, output logic [7:0] out);
    parameter type PT = logic [7:0];
    PT pt_var;
    always_comb begin
        pt_var = in;
        out = pt_var;
    end
endmodule
module M9_function_task(input int a, input int b, output int c);
    function int add(input int x, input int y);
        return x + y;
    endfunction
    task tsk(input int x, output int z);
        z = x * 2;
    endtask
    int tmp;
    always_comb begin
        tmp = add(a, b);
        tsk(tmp, tmp);
        c = tmp;
    end
endmodule
module M10_covergroup(input logic clk, input logic [3:0] in, output logic dbg);
    covergroup cg @(posedge clk);
        cp : coverpoint in {
            bins b0 = {4'h0, 4'h1};
        }
    endgroup
    cg cg_inst;
    always_ff @(posedge clk) begin
        cg_inst.sample();
        dbg <= in[0];
    end
endmodule
