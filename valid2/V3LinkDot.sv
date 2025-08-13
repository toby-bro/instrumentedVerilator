interface my_if;
    logic sig;
    modport mp (input sig);
endinterface
package util_pkg;
    typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
    typedef struct packed {logic [7:0] a; logic b;} s_t;
    class pkg_class;
        bit flag;
        function new();
            flag = 0;
        endfunction
    endclass
endpackage
module iface_user (
    input  logic in_sig,
    output logic out_sig
);
    my_if local_if();
    assign local_if.sig = in_sig;
    assign out_sig      = local_if.sig;
endmodule
module param_typedef_mod #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    typedef logic [WIDTH-1:0] word_t;
    word_t temp;
    assign temp     = in_data;
    assign out_data = temp;
    class fw_c;
        int dummy;
    endclass
    typedef fw_c fw_c_t;
    fw_c_t obj = new();
endmodule
module class_mod (
    input  logic i,
    output logic o
);
    virtual class base_c;
        pure virtual function int get();
        pure virtual task drive(input int v);
    endclass
    class derived_c extends base_c;
        int val;
        function new();
            super.new();
            val = 0;
        endfunction
        function int get();
            return val;
        endfunction
        task drive(input int v);
            val = v;
        endtask
    endclass
    derived_c d = new();
    always_comb begin
        d.drive(i);
        o = d.get();
    end
endmodule
module misc_features (
    input  logic        clk,
    output logic [3:0]  out_data
);
    import util_pkg::*;
    typedef logic [7:0] byte_t;
    byte_t mem [0:3];
    always_comb begin
        out_data = '0;
        foreach (mem[i]) begin
            out_data ^= mem[i][3:0];
        end
    end
    task automatic do_disable(input logic rstn, output logic done);
        begin : blk
            done = 0;
            if (rstn) disable blk;
        end
    endtask
endmodule
