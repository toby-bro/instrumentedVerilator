module top (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    always_comb begin
        if (GGGin) begin
            GGGsignal = 1'b1;
            //INJECT
        end else begin
            GGGsignal = 1'b0;
            //INJECT
        end
    end
endmodule

module GGG_always_ff (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    always_ff @(posedge GGGin) begin
        GGGsignal <= ~GGGsignal;
        //INJECT
    end
endmodule

module GGG_always_comb (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    always_comb begin
        GGGsignal = GGGin & 1'b1;
        //INJECT
    end
endmodule

module GGG_case (
    input logic [1:0] GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    always_comb begin
        case (GGGin)
            2'b00: GGGsignal = 1'b0;
            2'b01: GGGsignal = 1'b1;
            2'b10: GGGsignal = 1'b0;
            2'b11: GGGsignal = 1'b1;
            default: GGGsignal = 1'b0;
        endcase
        //INJECT
    end
endmodule

module GGG_for_loop (
    input logic GGGin,
    output logic GGGout
);
    logic [3:0] GGGsignal;
    assign GGGout = GGGsignal[0];

    always_comb begin
        for (int i = 0; i < 4; i = i + 1) begin
            GGGsignal[i] = GGGin;
            //INJECT
        end
    end
endmodule

module GGG_while_loop (
    input logic GGGin,
    output logic GGGout
);
    logic [3:0] GGGsignal;
    assign GGGout = GGGsignal[0];

    always_comb begin
        int i = 0;
        while (i < 4) begin
            GGGsignal[i] = GGGin;
            i = i + 1;
            //INJECT
        end
    end
endmodule

module GGG_task (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    task GGGtask;
        input logic GGGin_task;
        output logic GGGout_task;
        GGGout_task = ~GGGin_task;
        //INJECT
    endtask

    always_comb begin
        GGGtask(GGGin, GGGsignal);
    end
endmodule

module GGG_function (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    function logic GGGfunction(logic GGGin_func);
        GGGfunction = ~GGGin_func;
        //INJECT
    endfunction

    always_comb begin
        GGGsignal = GGGfunction(GGGin);
    end
endmodule

module GGG_generate (
    input logic GGGin,
    output logic GGGout
);
    logic GGGsignal;
    assign GGGout = GGGsignal;

    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin
            always_comb begin
                GGGsignal = GGGin;
                //INJECT
            end
        end
    endgenerate
endmodule

module GGG_struct (
    input logic GGGin,
    output logic GGGout
);
    typedef struct packed {
        logic a;
        logic b;
    } GGGstruct_t;

    GGGstruct_t GGGsignal;
    assign GGGout = GGGsignal.a;

    always_comb begin
        GGGsignal.a = GGGin;
        GGGsignal.b = ~GGGin;
        //INJECT
    end
endmodule

module GGG_array (
    input logic GGGin,
    output logic GGGout
);
    logic [3:0] GGGsignal;
    assign GGGout = GGGsignal[0];

    always_comb begin
        for (int i = 0; i < 4; i = i + 1) begin
            GGGsignal[i] = GGGin;
            //INJECT
        end
    end
endmodule
