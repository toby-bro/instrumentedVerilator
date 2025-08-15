module unpacked_array_example(
    input  logic [1:0] in0,
    input  logic [1:0] in1,
    output logic [1:0] out0,
    output logic [1:0] out1
);
    logic [1:0] ua[0:1] /*verilator split_var*/;
    always_comb begin
        ua[0]    = in0;
        ua[1][0] = ua[0][0];
        ua[1][1] = ~ua[0][1];
        out0     = ua[1];
        ua[0]    = in1;
        out1     = ua[0];
    end
endmodule
module packed_var_example(
    input  logic       in_cond,
    input  logic       in_bit,
    input  logic [2:0] in_bus,
    output logic [3:0] out_bus
);
    logic [3:0] pvar /*verilator split_var*/;
    always_comb begin
        if (in_cond) begin
            pvar = 4'b0;
        end else begin
            pvar[3]   = in_bit;
            pvar[2:0] = in_bus;
        end
        out_bus = pvar;
    end
endmodule
module unpacked_struct_example(
    input  logic       a,
    input  logic [2:0] b,
    output logic       y_out
);
    typedef struct {
        logic       x;
        logic [2:0] y;
    } unps_t;
    unps_t us[0:1] /*verilator split_var*/;
    always_comb begin
        us[0].x = a;
        us[0].y = b;
        us[1].x = ~us[0].x;
        us[1].y =  us[0].y;
        y_out   =  us[1].y[0];
    end
endmodule
module packed_struct_example(
    input  logic [2:0] in_p,
    input  logic       in_q,
    output logic       out_q
);
    typedef struct packed {
        logic [2:0] p;
        logic       q;
    } pack_s;
    pack_s ps /*verilator split_var*/;
    always_comb begin
        ps.p  = in_p;
        ps.q  = in_q;
        out_q = ps.q;
    end
endmodule
module bitfield_example(
    input  logic [7:0] in_byte,
    output logic       out_bit
);
    logic [7:0] big /*verilator split_var*/;
    always_comb begin
        big     = in_byte;
        out_bit = big[3];
    end
endmodule
module nested_array_example(
    input  logic [7:0] in_a,
    output logic [7:0] out_a
);
    logic [7:0] narray[0:1][0:1] /*verilator split_var*/;
    always_comb begin
        narray[0][0] = in_a;
        narray[1][0] = narray[0][0];
        out_a        = narray[1][0];
    end
endmodule
module port_split_example(
    input  logic [3:0] port_in,
    output logic [3:0] port_out
);
    always_comb begin
        port_out = {port_in[2:0], port_in[3]};
    end
endmodule
module func_reference_example(
    input  logic       sel,
    input  logic [3:0] din,
    output logic [3:0] dout
);
    logic [3:0] fun_var /*verilator split_var*/;
    function automatic logic [3:0] foo(input logic s);
        if (s) foo = 4'hA;
        else   foo = 4'h5;
    endfunction
    always_comb begin
        fun_var = din ^ foo(sel);
        dout    = fun_var;
    end
endmodule
module auto_split_candidate(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] vec8 /*verilator split_var*/;
    always_comb begin
        vec8[7:4] = in_data[7:4];
        vec8[3:0] = in_data[3:0];
        out_data  = vec8;
    end
endmodule
module task_ref_example(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] tvar /*verilator split_var*/;
    task automatic modify(ref logic [7:0] r);
        r = ~r;
    endtask
    always_comb begin
        tvar = in_data;
        modify(tvar);
        out_data = tvar;
    end
endmodule
