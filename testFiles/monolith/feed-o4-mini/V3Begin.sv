interface my_ifc;
    logic sig;
    modport mp (input sig);
endinterface
module mod_assign(input logic a, b, output logic y);
    assign y = a & b;
endmodule
module mod_if(input logic clk, rst, in1, output logic out);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            out <= 1'b0;
        end else begin
            if (in1) begin
                out <= 1'b1;
            end else begin
                out <= 1'b0;
            end
        end
    end
endmodule
module mod_begin(input logic a, b, output logic y, z);
    always_comb begin
        begin
            y = a;
        end
        begin
            z = b;
        end
    end
endmodule
module mod_foreach(input logic [7:0] din, output logic [7:0] dout);
    logic [7:0] arr [0:3];
    logic [31:0] i;
    always_comb begin
        foreach (arr[i]) begin
            arr[i] = din + i;
        end
        dout = arr[0];
    end
endmodule
module mod_for_while(input logic [3:0] cnt, output logic done);
    logic [3:0] i;
    always_comb begin
        i = 0;
        for (; i < cnt; i = i + 1) begin
        end
        while (i > 0) begin
            i = i - 1;
        end
        done = (i == 0);
    end
endmodule
module mod_function(input logic [7:0] in, output logic [7:0] out);
    function automatic logic [7:0] func(input logic [7:0] x);
        logic [7:0] tmp;
        begin
            tmp = x + 1;
            func = tmp;
        end
    endfunction
    always_comb begin
        out = func(in);
    end
endmodule
module mod_task(input logic [7:0] in, output logic [7:0] out);
    task automatic tsk(input logic [7:0] x, output logic [7:0] y);
        logic [7:0] tmp;
        begin
            tmp = x << 1;
            y = tmp;
        end
    endtask
    always_comb begin
        tsk(in, out);
    end
endmodule
module mod_typedef(input logic [3:0] in, output logic [3:0] out);
    typedef logic [3:0] nib;
    nib tmp;
    always_comb begin
        tmp = in;
        out = tmp;
    end
endmodule
module mod_generate(input logic [3:0] in, output logic [3:0] out);
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin: genblk
            assign out[i] = in[i];
        end
    endgenerate
endmodule
module mod_cover(input logic clk, input logic in, output logic out);
    covergroup cg @(posedge clk);
        coverpoint in;
    endgroup
    cg cg_inst = new();
    always_ff @(posedge clk) begin
        cg_inst.sample();
        out <= in;
    end
endmodule
module mod_interface(input logic in, output logic out);
    my_ifc ifc_inst();
    assign ifc_inst.sig = in;
    always_comb begin
        out = ifc_inst.sig;
    end
endmodule
module mod_gate(input logic a, b, output logic y);
    and u_and (y, a, b);
endmodule
