module mod_params #(parameter int WIDTH = 8, parameter logic [15:0] CONST_VAL = 16'hABCD)
                   (input logic [WIDTH-1:0] data_in, output logic [WIDTH-1:0] data_out);
    localparam int HALF = WIDTH/2;
    assign data_out = {{HALF{data_in[HALF-1]}}, data_in[HALF-1:0]};
endmodule
module mod_methods(input logic trigger, output logic flag);
    logic internal_var;
    function void __Vconfigure(input bit first_flag);
        if (first_flag)
            internal_var = 1'b1;
        else
            internal_var = 1'b0;
    endfunction
    function void __vlCoverInsert(input int countp, input bit enable, input string fname, input int line, input int col, input string hier, input string page, input string comment, input string linescov);
        if (enable)
            flag = |{countp, line, col};
        else
            flag = 1'b0;
    endfunction
    function automatic int __vlCoverToggleInsert(input int begin_idx, input int end_idx, input bit ranged, input int countp, input bit enable, input string fname, input int line, input int col, input string hier, input string page, input string comment);
        return begin_idx + end_idx + countp;
    endfunction
    function void __Vserialize(output logic [7:0] os);
        os = 8'hA5;
    endfunction
    function void __Vdeserialize(input logic [7:0] os);
        flag = os[0];
    endfunction
    always_comb begin
        __Vconfigure(trigger);
        __vlCoverInsert(1, trigger, "f", 1, 1, "h", "p", "c", "l");
        flag = internal_var;
    end
endmodule
module mod_enums(input logic sel, output logic [2:0] val);
    typedef enum logic [2:0] {ZERO = 3'd0, ONE = 3'd1, TWO = 3'd2} small_e;
    typedef enum logic [65:0] {BIG0 = 66'd0, BIG1 = 66'd1} big_e;
    small_e e;
    always_comb begin
        e = sel ? ONE : ZERO;
        val = e;
    end
endmodule
module mod_structs(input logic [3:0] inA, output logic [3:0] outA);
    typedef struct packed { logic [1:0] a; logic b; logic [0:0] c; } packed_s;
    typedef struct { logic x; logic [7:0] y; } unpacked_s;
    packed_s ps;
    unpacked_s us;
    always_comb begin
        ps = '{a: inA[1:0], b: inA[2], c: inA[3]};
        us.x = ps.b;
        us.y = {ps.a, ps.c};
        outA = {us.x, us.y[2:0]};
    end
endmodule
module mod_union(input logic [7:0] din, output logic [7:0] dout);
    typedef union packed { logic [7:0] u8; logic [15:0] u16; } union_p;
    union_p u;
    always_comb begin
        u.u8 = din;
        dout = u.u8;
    end
endmodule
module mod_arrays(input logic [1:0] idx, output logic [7:0] outA);
    logic [7:0] static_array [0:3];
    logic [7:0] dyn_array [];
    function void init_array();
        static_array[0] = 8'h00;
        static_array[1] = 8'h11;
        static_array[2] = 8'h22;
        static_array[3] = 8'h33;
        dyn_array = new[4];
        dyn_array[0] = 8'h44;
    endfunction
    always_comb begin
        init_array();
        if (idx < 4)
            outA = static_array[idx];
        else
            outA = dyn_array[0];
    end
endmodule
module mod_bitops(input logic [31:0] data_in, input logic [4:0] offset, output logic [7:0] slice8);
    function logic [7:0] get_bits(input logic [31:0] data, input int off);
        get_bits = data[off +: 8];
    endfunction
    always_comb begin
        slice8 = get_bits(data_in, offset);
    end
endmodule
