module forceable_net(input logic in, output logic out);
    logic in__VforceEn;
    logic in__VforceVal;
    wire in__VforceRd;
    initial in__VforceEn = 0;
    assign in__VforceRd = in__VforceEn ? in__VforceVal : in;
    assign out = in__VforceRd;
endmodule
module override_comb(input logic a, b, output logic out);
    logic overrideEn;
    logic overrideVal;
    logic vrd;
    initial overrideEn = 0;
    always_comb vrd = overrideEn ? overrideVal : a;
    assign out = vrd & ~b;
endmodule
module seq_force(input logic clk, input logic in_val, input logic forceIn, input logic rel, output logic out);
    logic net;
    logic net__VforceEn = 0;
    logic net__VforceVal;
    wire net__VforceRd;
    assign net__VforceRd = net__VforceEn ? net__VforceVal : net;
    always_ff @(posedge clk) begin
        if (forceIn) begin
            net__VforceEn <= 1;
            net__VforceVal <= in_val;
        end
        else if (rel) begin
            net__VforceEn <= 0;
        end
        else begin
            net <= net__VforceRd;
        end
    end
    assign out = net;
endmodule
module ranged_update(input logic [3:0] a, input logic [3:0] val, input logic en, output logic [3:0] out);
    logic [3:0] rd;
    assign rd = (en & val) | (~en & a);
    assign out = rd;
endmodule
module function_force(input logic en, input logic [7:0] val, input logic [7:0] orig, output logic [7:0] out);
    function logic [7:0] forcedUpdate(input logic en_f, input logic [7:0] val_f, input logic [7:0] orig_f);
        forcedUpdate = en_f ? val_f : orig_f;
    endfunction
    assign out = forcedUpdate(en, val, orig);
endmodule
module multi_force_gen(input logic clk, output logic [1:0] flags);
    genvar i;
    generate
        for (i = 0; i < 2; i = i+1) begin: genblk
            logic sig;
            logic sig__VforceEn;
            logic sig__VforceVal;
            logic sig__VforceRd;
            initial sig__VforceEn = 0;
            always_comb sig__VforceRd = sig__VforceEn ? sig__VforceVal : sig;
            assign flags[i] = sig__VforceRd;
        end
    endgenerate
endmodule
module complex_sensitivity(input logic clk, input logic en, input logic val, output logic rd);
    logic sig;
    always @(posedge clk or posedge en or negedge val) begin
        if (en) rd <= val;
        else rd <= sig;
    end
endmodule
module proc_force(input logic a, input logic b, output logic out);
    logic c;
    task automatic updateC;
        c = a & b;
    endtask
    always_comb begin
        updateC();
        out = c;
    end
endmodule
