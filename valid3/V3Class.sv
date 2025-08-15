module class_hierarchy_mod(
    input  logic [7:0] i_data,
    output logic [7:0] o_data
);
    interface class IDataProcessor;
        pure virtual function logic [7:0] process(logic [7:0] x);
    endclass
    class BaseProcessor implements IDataProcessor;
        static int internal;
        static task automatic mutate(ref logic [7:0] y);
            y = y ^ 8'hAA;
        endtask
        function logic [7:0] process(logic [7:0] x);
            internal = x;
            return x + 1;
        endfunction
    endclass
    class AdvancedProcessor extends BaseProcessor implements IDataProcessor;
        function logic [7:0] process(logic [7:0] x);
            logic [7:0] tmp;
            tmp = super.process(x);
            return tmp + 1;
        endfunction
    endclass
    always_comb begin
        automatic AdvancedProcessor proc = new();
        logic [7:0] val;
        val = proc.process(i_data);
        BaseProcessor::mutate(val);
        o_data = val;
    end
endmodule
module packed_struct_mod(
    input  logic        clk,
    input  logic [31:0] din,
    output logic [31:0] dout
);
    typedef struct packed {
        logic [7:0]  a;
        logic [23:0] b;
    } small_t;
    (* public *) typedef struct packed {
        small_t      nested;
        logic [31:0] c;
    } big_t;
    typedef union packed {
        logic [31:0] word;
        small_t      small_u;
    } u_t;
    big_t big_reg;
    u_t   uni_reg;
    always_ff @(posedge clk) begin
        big_reg.c    <= din;
        uni_reg.word <= din;
        dout         <= big_reg.c ^ uni_reg.word;
    end
endmodule
module initial_blocks_mod(
    input  logic in_sig,
    output logic out_sig
);
    logic store;
    initial begin
        store = 1'b0;
    end
    always_comb begin
        out_sig = store & in_sig;
    end
endmodule
module dpi_decl_mod(
    input  logic [3:0] a,
    output logic [3:0] b
);
    import "DPI-C" context function int add_one(input int unsigned i);
    assign b = a;
endmodule
