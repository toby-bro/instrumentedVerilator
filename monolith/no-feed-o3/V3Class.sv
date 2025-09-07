module class_extend_mod(
    input  logic             clk,
    input  logic [3:0]       din,
    output logic [3:0]       dout
);
    virtual class iface;
        pure virtual function void          set(input logic [3:0] v);
        pure virtual function logic [3:0]   get();
    endclass
    class base implements iface;
        logic [3:0] val;
        static int  counter;
        function void set(input logic [3:0] v);
            val = v;
            counter++;
        endfunction
        function logic [3:0] get();
            return val;
        endfunction
    endclass
    class child extends base;
        function void incr();
            val = val + 1;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        child obj = new();
        obj.set(din);
        dout <= obj.get();
    end
endmodule
module packed_typedef_mod(
    input  logic [7:0] in_a,
    output logic [7:0] out_a
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } packed_s;
    packed_s s;
    always_comb begin
        s.hi  = in_a[7:4];
        s.lo  = in_a[3:0];
        out_a = {s.hi, s.lo};
    end
endmodule
module union_mod(
    input  logic [7:0] bus,
    output logic [7:0] out_bus
);
    typedef union packed {
        logic [7:0] byte;
        struct packed {
            logic [3:0] lo;
            logic [3:0] hi;
        } nibbles;
    } union_t;
    union_t u;
    always_comb begin
        u.byte  = bus;
        out_bus = {u.nibbles.hi, u.nibbles.lo};
    end
endmodule
module init_static_mod(
    input  logic clk,
    input  logic a,
    output logic b
);
    logic r;
    initial begin
        r = 1'b0;
    end
    always_ff @(posedge clk) begin
        r <= a;
    end
    assign b = r;
endmodule
module init_auto_mod(
    input  logic clk,
    input  logic i,
    output logic o
);
    logic r;
    initial automatic begin
        r = 1'b0;
    end
    always_ff @(posedge clk) begin
        r <= i;
    end
    assign o = r;
endmodule
module covergroup_mod(
    input  logic       clk,
    input  logic [1:0] sig,
    output logic       dummy
);
    bit started;
    covergroup cg_grp @(posedge clk);
        option.per_instance = 1;
        sig_cp : coverpoint sig;
    endgroup
    cg_grp cg_inst = new();
    assign dummy = started;
endmodule
module task_static_mod(
    input  logic             clk,
    input  logic [3:0]       data_in,
    output logic [3:0]       data_out
);
    task automatic work(input logic [3:0] x, output logic [3:0] y);
        static int count;
        count++;
        y = x + count[3:0];
    endtask
    always_ff @(posedge clk) begin
        logic [3:0] temp;
        work(data_in, temp);
        data_out <= temp;
    end
endmodule
module class_static_task_mod(
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class compute;
        static function logic [7:0] swap(input logic [7:0] value);
            return {value[3:0], value[7:4]};
        endfunction
    endclass
    always_ff @(posedge clk) begin
        dout <= compute::swap(din);
    end
endmodule
module toggle_func_static_mod(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    function logic toggle(input logic x);
        static logic state = 1'b0;
        state = ~state;
        return state & x;
    endfunction
    always_ff @(posedge clk) begin
        out_sig <= toggle(in_sig);
    end
endmodule
module accum_class_mod(
    input  logic       clk,
    input  logic [3:0] val_in,
    output logic [3:0] val_out
);
    class accum;
        static int total = 0;
        task automatic add(input int v);
            total += v;
        endtask
        function int get();
            return total;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        accum h = new();
        h.add(val_in);
        val_out <= h.get()[3:0];
    end
endmodule
module diamond_mod(
    input  logic       clk,
    input  logic [3:0] din,
    output logic [3:0] dout
);
    virtual class ic1;
        pure virtual function logic [3:0] get();
    endclass
    virtual class ic2;
        pure virtual function logic [3:0] get2();
    endclass
    class baseA implements ic1;
        logic [3:0] v;
        function new(logic [3:0] val);
            v = val;
        endfunction
        function logic [3:0] get();
            return v;
        endfunction
    endclass
    class baseB implements ic2;
        logic [3:0] v;
        function new(logic [3:0] val);
            v = val;
        endfunction
        function logic [3:0] get2();
            return v;
        endfunction
    endclass
    class derived extends baseA implements ic2;
        baseB b;
        function new(logic [3:0] val);
            super.new(val);
            b = new(val);
        endfunction
        function logic [3:0] get2();
            return b.get2();
        endfunction
    endclass
    always_ff @(posedge clk) begin
        derived obj = new(din);
        dout <= obj.get() ^ obj.get2();
    end
endmodule
import "DPI-C" function int svdpi_add(input int a, input int b);
module dpi_mod(
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    always_comb begin
        y = svdpi_add(a, b);
    end
endmodule
module class_typedef_mod(
    input  logic       clk,
    input  logic [3:0] inp,
    output logic [3:0] outp
);
    class cont;
        typedef struct packed {logic [3:0] v;} data_t;
        function data_t create(input logic [3:0] vv);
            data_t tmp;
            tmp.v = vv;
            return tmp;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        cont c = new();
        cont::data_t d = c.create(inp);
        outp <= d.v;
    end
endmodule
