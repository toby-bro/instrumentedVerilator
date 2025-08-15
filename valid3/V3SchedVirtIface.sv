interface vif_ifc;
    logic sig1;
    logic sig2;
    logic sig3;
endinterface
class my_c;
    bit val;
endclass
module vif_cont_assign(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    always_ff @(posedge clk) begin
        vif.sig2 <= in_sig;
        out_sig  <= vif.sig1;
    end
endmodule
module vif_nbassign(
    input  logic clk,
    input  logic din,
    output logic dout
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    always_ff @(posedge clk) begin
        vif.sig1 <= din;
        dout     <= vif.sig2;
    end
endmodule
module vif_while_if(
    input  logic clk,
    input  logic reset_n,
    output logic out_flag
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    integer i;
    always_comb begin
        i = 0;
        out_flag = 1'b0;
        while (i < 3) begin
            out_flag = out_flag ^ i[0];
            i = i + 1;
        end
    end
    always_ff @(posedge clk) begin
        if (!reset_n) begin
            vif.sig3 <= 1'b0;
        end else begin
            vif.sig3 <= out_flag;
        end
    end
endmodule
module vif_function(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    function automatic logic func(input logic x);
        logic tmp;
        tmp = x;
        return tmp;
    endfunction
    always_ff @(posedge clk) begin
        vif.sig1 <= in_sig;
        out_sig  <= func(in_sig);
    end
endmodule
module vif_jump(
    input  logic clk,
    input  logic ena,
    input  logic cond,
    output logic result
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    always_ff @(posedge clk) begin
        result <= 1'b0;
        if (ena) begin
            vif.sig3 <= cond;
            result   <= 1'b1;
        end
    end
endmodule
module vif_class(
    input  logic clk,
    input  logic in_data,
    output logic out_data
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    my_c c = new();
    always_comb begin
        c.val = in_data;
    end
    always_ff @(posedge clk) begin
        vif.sig1 <= c.val;
        out_data <= vif.sig1;
    end
endmodule
module vif_if_cond(
    input  logic clk,
    input  logic in1,
    input  logic in2,
    output logic out1
);
    vif_ifc if_inst();
    virtual vif_ifc vif = if_inst;
    always_ff @(posedge clk) begin
        vif.sig1 <= in1;
        if (vif.sig1) begin
            vif.sig3 <= in2;
            out1     <= vif.sig3;
        end else begin
            vif.sig3 <= 1'b0;
            out1     <= vif.sig1;
        end
    end
endmodule
