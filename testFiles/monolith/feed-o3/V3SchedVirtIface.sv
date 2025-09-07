interface simple_if;
    logic        a;
    logic        b;
    logic [7:0]  data;
endinterface
module iface_cont_assign (
    input  logic in_sig,
    output logic out_sig
);
    simple_if vif_inst();
    assign vif_inst.a = in_sig;
    assign out_sig    = vif_inst.b;
endmodule
module iface_always_comb (
    input  logic in_sig,
    output logic out_sig
);
    simple_if vif_inst();
    always_comb begin
        vif_inst.a = in_sig;
        vif_inst.b = ~in_sig;
        out_sig = vif_inst.a & vif_inst.b;
    end
endmodule
module iface_if_condition (
    input  logic in_sig,
    output logic out_sig
);
    simple_if vif_inst();
    always_comb begin
        if ((vif_inst.a = in_sig)) begin
            out_sig = 1'b1;
        end else begin
            out_sig = 1'b0;
        end
    end
endmodule
module iface_loop_increment (
    input  logic [3:0] max_cnt,
    output logic       done
);
    simple_if vif_inst();
    always_comb begin
        done = 1'b0;
        for (vif_inst.data = 0; vif_inst.data < max_cnt; vif_inst.data = vif_inst.data + 1) begin
        end
        done = 1'b1;
    end
endmodule
module vif_internal_virtual (
    input  logic in_sig,
    output logic out_sig
);
    virtual simple_if vif;
    always_comb begin
        if (vif != null) begin
            vif.a = in_sig;
            out_sig = vif.a;
        end else begin
            out_sig = 1'b0;
        end
    end
endmodule
