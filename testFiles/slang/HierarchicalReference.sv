interface simple_if;
    logic sig;
    modport m_in  (input  sig);
    modport m_drv (output sig);
endinterface
module leaf_dev (
    input  logic ctrl_in,
    output logic dummy_out,
    simple_if.m_in if_port
);
    assign dummy_out = ctrl_in ^ if_port.sig;
endmodule
module iface_hier_test (
    input  logic in,
    output logic out
);
    simple_if if_inst ();
    assign if_inst.sig = in;
    leaf_dev devs [0:3] (
        .ctrl_in  (in),
        .dummy_out(),
        .if_port  (if_inst)
    );
    assign out = devs[1].if_port.sig;
    logic root_ref;
    assign root_ref = $root.iface_hier_test.devs[0].if_port.sig;
    logic join_sig;
    assign join_sig = devs[0].if_port.sig ?
                      $root.iface_hier_test.devs[2].if_port.sig :
                      devs[3].if_port.sig;
endmodule
module upward_test (
    input  logic in,
    output logic out
);
    logic root_sig;
    assign root_sig = in;
    if (1) begin : level1
        logic l1;
        assign l1 = $root.upward_test.root_sig;
        if (1) begin : level2
            logic l2;
            assign l2 = level1.l1;
            assign out = l2;
        end
    end
endmodule
module genblk_example (
    input  logic in,
    output logic out
);
    if (1) begin : g
        for (genvar i = 0; i < 4; i++) begin : gb
            logic gb_sig;
            assign gb_sig = in;
        end
    end
    logic sel_sig;
    assign sel_sig = g.gb[2].gb_sig;
    assign out     = sel_sig;
    logic [1:0] range_vec;
    assign range_vec = { g.gb[2].gb_sig, g.gb[1].gb_sig };
endmodule
