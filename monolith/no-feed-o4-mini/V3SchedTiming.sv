module remap_domains #(parameter W = 8, parameter N = 4) (
    input  logic [W-1:0] in_arr [N],
    output logic [W-1:0] out_arr [N]
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_map
            assign out_arr[i] = in_arr[N-1-i];
        end
    endgenerate
endmodule
module resume_module (
    input  logic clk,
    input  logic rst,
    output logic done
);
    event trigger_event;
    always_ff @(posedge clk) begin
        if (rst) begin
            -> trigger_event;
        end
    end
    always @(trigger_event) begin
        done <= 1'b1;
    end
endmodule
module commit_module (
    input  logic sig_a,
    input  logic sig_b,
    output logic sig_c
);
    always_ff @(posedge sig_a or posedge sig_b) begin
        if (!sig_b) begin
            sig_c <= 1'b1;
        end else begin
            sig_c <= 1'b0;
        end
    end
endmodule
module prepare_timing (
    input  logic        clk,
    input  logic        enable,
    output logic [7:0]  data_out
);
    logic [7:0] bus;
    always_ff @(posedge clk) begin
        if (enable) begin
            wait (bus[0]);
            bus <= 8'hFF;
        end
    end
    assign data_out = bus;
endmodule
module transform_forks (
    input  logic        start,
    output logic [3:0]  result
);
    always_ff @(posedge start) begin
        fork
            begin : inner1
                result <= 4'd1;
            end
            begin : inner2
                result <= 4'd2;
            end
        join
    end
endmodule
module remap_locals (
    input  logic [3:0] a,
    output logic [3:0] b,
    inout  logic [3:0] c
);
    function automatic logic [3:0] myfunc (
        input logic [3:0] x,
        inout logic [3:0] y
    );
        logic [3:0] z;
        z = x + y;
        y = z;
        return z;
    endfunction
    always_comb begin
        b = myfunc(a, c);
    end
endmodule
module dynamic_event (
    input  logic trigger_in,
    output logic ack
);
    event dyn_event;
    task automatic fire_event (
        input logic trig
    );
        if (trig) begin
            -> dyn_event;
        end
    endtask
    always_ff @(posedge trigger_in) begin
        fire_event(trigger_in);
    end
    always @(dyn_event) begin
        ack <= 1'b1;
    end
endmodule
