module specify_full_path (
    input  wire a,
    output wire y
);
    specify
        specparam t_rise = 1, t_fall = 2;
        (a *> y) = (t_rise, t_fall);
    endspecify
endmodule
module specify_parallel_path (
    input  wire [3:0] d,
    output wire [3:0] q
);
    specify
        (d => q) = 3;
    endspecify
endmodule
module specify_conditional_path (
    input  wire a,
    input  wire b,
    output wire y
);
    specify
        if (a && b) (a => y) = 2;
        ifnone (a => y) = 3;
    endspecify
endmodule
module specify_edge_sensitive (
    input  wire clk,
    input  wire data,
    output wire q
);
    specify
        specparam t_pd = 1;
        (posedge clk => (q : data)) = t_pd;
    endspecify
endmodule
module specify_pulsestyle (
    input  wire in1,
    output wire out1
);
    specify
        pulsestyle_onevent out1;
    endspecify
endmodule
module specify_timing_checks (
    input  wire clk,
    input  wire d,
    output logic notifier
);
    specify
        $setup (posedge d   , posedge clk, 3, notifier);
        $hold  (posedge clk , posedge d  , 2, notifier);
        $width (negedge clk , 4, 0, notifier);
    endspecify
endmodule
module specify_implicit_net (
    input  wire sig,
    input  wire clk,
    output logic notifier
);
    specify
        $setup   (posedge sig        , posedge unknown_clk, 1, notifier);
        $hold    (posedge unknown_clk, posedge sig       , 1, notifier);
        $period  (posedge clk        , 10, notifier);
        $nochange(posedge clk, sig, 5, 5, notifier);
    endspecify
endmodule
module specify_extended_timing_checks (
    input  wire a,
    input  wire clk,
    output wire b,
    output logic notifier
);
    specify
        (posedge clk => (b : a)) = 1;
        $setuphold(posedge a, posedge clk, 2, 3, notifier);
        $recrem   (posedge b, posedge clk, 1, 2, notifier);
        $skew     (posedge clk, posedge a, 1, notifier);
        $timeskew (posedge clk, posedge b, 2, notifier, 3, 3);
        $fullskew (posedge clk, posedge a, 2, 2, notifier, 3, 3);
    endspecify
endmodule
