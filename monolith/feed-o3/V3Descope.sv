//====================================================
module m_child (
    input  logic [3:0] in,
    output logic [3:0] internal_sig
);
    assign internal_sig = in + 4'd1;
endmodule
//====================================================
module m_scope (
    input  logic        sel,
    input  logic [3:0]  in0,
    output logic [3:0]  y
);
    wire [3:0] w_internal0;
    wire [3:0] w_internal1;
    m_child u0 (.in(in0),   .internal_sig(w_internal0));
    m_child u1 (.in(~in0),  .internal_sig(w_internal1));
    function static logic [3:0] static_get0;
        static_get0 = u0.internal_sig;
    endfunction
    if (1) begin : gblkA
        function automatic logic [3:0] dup_func (input logic [3:0] a); /*verilator public*/
            dup_func = a + 4'd2;
        endfunction
    end
    if (1) begin : gblkB
        function automatic logic [3:0] dup_func (input logic [3:0] a); /*verilator public*/
            dup_func = a + 4'd3;
        endfunction
    end
    wire [3:0] resA = gblkA.dup_func(w_internal0);
    wire [3:0] resB = gblkB.dup_func(w_internal1);
    wire [3:0] st_v = static_get0();
    assign y = sel ? resA : (resB ^ st_v);
endmodule
//====================================================
module m_class_mod (
    input  logic [7:0] in,
    output logic [7:0] out
);
    class myClass;
        int val;
        function new (int v);
            val = v;
        endfunction
        function int get ();
            get = val;
        endfunction
        static function int add (input int a, b);
            add = a + b;
        endfunction
    endclass
    always_comb begin
        myClass obj = new(in);
        out = myClass::add(obj.get(), 1);
    end
endmodule
