module specify_basic(input  wire in1,
                     output wire out1);
    specify
        (in1 *> out1) = 3;
    endspecify
endmodule
module specify_edge(input  wire clk,
                    output wire q);
    specify
        (posedge clk => q) = (1,2,3);
    endspecify
endmodule
module specify_conditional(input  wire x,
                           input  wire y,
                           output wire z);
    wire cond = y;
    specify
        if (cond) (x *> z) = (2,3);
    endspecify
endmodule
module specify_ifnone(input  wire p,
                      output wire r);
    specify
        ifnone (p *> r) = 4;
    endspecify
endmodule
module specify_specparam(input  wire u,
                         output wire v);
    specparam DELAY = 5;
    specify
        (u *> v) = DELAY;
    endspecify
endmodule
module specify_pulsestyle(input  wire s,
                          output wire t);
    specify
        pulsestyle_onevent t;
        (s *> t) = 1;
    endspecify
endmodule
module specify_timingcheck(input  wire clk,
                           input  wire d,
                           output wire q);
    reg notifier;
    specify
        $setup(posedge d, posedge clk, 3, notifier);
        $hold(posedge clk, posedge d, 2, notifier);
        (clk *> q) = 1;
    endspecify
endmodule
