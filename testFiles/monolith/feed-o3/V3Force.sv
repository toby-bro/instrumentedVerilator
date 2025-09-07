module force_scalar_reg (
    input  logic clk,
    input  logic trigger,
    output logic res
);
    (* forceable *) logic data;
    logic other;
    always_ff @(posedge clk) begin
        if (trigger) begin
            force data = other;
            other <= ~other;
        end else begin
            release data;
        end
        res <= data;
    end
endmodule
module force_wire_continuous (
    input  logic a,
    input  logic b,
    input  logic ctrl,
    output logic y
);
    (* forceable *) wire w;
    assign w = a & b;
    always @* begin
        if (ctrl) begin
            force w = 1'b1;
        end else begin
            release w;
        end
        y = w;
    end
endmodule
module force_vector_whole (
    input  logic        clk,
    input  logic        act,
    output logic [7:0]  out
);
    (* forceable *) logic [7:0] v;
    always_ff @(posedge clk) begin
        if (act) begin
            force v = 8'hA5;
        end else begin
            release v;
        end
        out <= v;
    end
endmodule
module force_with_task (
    input  logic clk,
    input  logic act,
    output logic outp
);
    (* forceable *) logic regval;
    logic shadow;
    task automatic apply_force (input logic val);
        shadow = val;
        force regval = shadow;
    endtask
    task automatic release_force ();
        release regval;
    endtask
    always_ff @(posedge clk) begin
        if (act) begin
            apply_force(~regval);
        end else begin
            release_force();
        end
        outp <= regval;
    end
endmodule
module force_real_demo (
    input  logic clk,
    input  logic req,
    output real  r_out
);
    (* forceable *) real r;
    always_ff @(posedge clk) begin
        if (req) begin
            force r = 3.14;
        end else begin
            release r;
        end
        r_out <= r;
    end
endmodule
