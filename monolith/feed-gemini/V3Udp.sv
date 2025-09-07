primitive CombUdpBase (output out_val, input in_a, input in_b);
    table
       0 0 : 1;
       0 1 : 0;
       1 0 : x;
       1 1 : 1;
    endtable
endprimitive
primitive CombUdpInputDontCare (output out_q, input in_c, input in_d);
    table
       1 ? : 1;
       ? 1 : 1;
       0 0 : 0;
    endtable
endprimitive
primitive CombUdpInputX (output result_x, input val_in);
    table
       x : x;
       0 : 0;
       1 : 1;
    endtable
endprimitive
primitive SeqUdpPosEdge_DFF (output reg Q, input CLK, input D);
    initial Q = 1'b0;
    table
       (01) 0 : ?         : 0;
       (01) 1 : ?         : 1;
       ?  0 : ? : -;
       ?  1 : ? : -;
    endtable
endprimitive
primitive SeqUdpBothEdges_TFF (output reg Q, input T, input CLK);
    initial Q = 1'b0;
    table
       0 (01) : ?         : 0;
       1 (01) : 0         : 1;
       1 (01) : 1         : 0;
       0 (10) : ?         : 0;
       1 (10) : 0         : 1;
       1 (10) : 1         : 0;
       ? 0    : ?         : -;
       ? 1    : ?         : -;
    endtable
endprimitive
primitive SeqUdpNegEdge_SR_Latch (output reg Q, input S, input R, input CLK);
    initial Q = 1'bx;
    table
       1 0 (10) : ? : 1;
       0 1 (10) : ? : 0;
       0 0 (10) : ? : -;
       1 1 (10) : ? : x;
       ? ? 0    : ? : -;
       ? ? 1    : ? : -;
    endtable
endprimitive
primitive SeqUdpSpecialEdges_Gate (output reg Q, input D, input CLK);
    initial Q = 1'b0;
    table
       0 (?0) : ? : 0;
       1 (0?) : ? : 1;
       ? 0    : ? : -;
       ? 1    : ? : -;
    endtable
endprimitive
primitive SeqUdpAnyEdge_Toggle (output reg Q, input CLK, input E);
    initial Q = 1'b0;
    table
        *  1 : 0         : 1;
        *  1 : 1         : 0;
        ?  0 : ?         : -;
    endtable
endprimitive
