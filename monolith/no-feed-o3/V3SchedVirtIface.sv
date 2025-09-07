interface simple_ifc;
    wire        a_w;
    wire        b_w;
    logic       a_l;
    logic       b_l;
    logic [3:0] data_l;
endinterface
module intf_assignw (
    input  logic in1,
    output logic out1,
    simple_ifc  sif
);
    assign sif.a_w = in1;   
    assign out1    = sif.a_w;
endmodule
module virt_nb_assign (
    input  logic clk,
    input  logic d,
    output logic q,
    simple_ifc  real_if
);
    virtual simple_ifc vif;
    initial begin
        vif = real_if;      
    end
    always_ff @(posedge clk) begin
        vif.b_l <= d;       
        q       <= vif.b_l;
    end
endmodule
module dpi_writer (
    input  logic in2,
    output logic out2,
    simple_ifc  ifc_port
);
    virtual simple_ifc v2;
    initial begin
        v2 = ifc_port;
    end
    export "DPI-C" function dpi_func;
    function void dpi_func (input int dummy);
        v2.data_l = dummy[3:0];   
    endfunction
    assign out2 = in2;
endmodule
module loop_writer (
    input  logic clk,
    input  logic rst_n,
    output logic o,
    simple_ifc  i_face
);
    virtual simple_ifc vif3;
    initial begin
        vif3 = i_face;
    end
    logic flag;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            flag     <= 1'b0;
            vif3.a_l <= 1'b0;
        end else begin
            if (flag) begin
                vif3.a_l <= ~vif3.a_l;
            end
            while (flag) begin       
                vif3.b_l <= 1'b0;
                flag     <= 1'b0;
                break;
            end
        end
    end
    assign o = vif3.a_l;
endmodule
module continuous_virtual (
    input  logic in3,
    output logic out3,
    simple_ifc  real_if
);
    virtual simple_ifc vifc;
    initial begin
        vifc = real_if;
    end
    assign vifc.b_w = in3;   
    assign out3     = vifc.b_w;
endmodule
