module force_simple_mod(
    input  logic en,
    output logic q
);
    logic a;
    always_comb begin
        if (en) begin
            force a = 1'b1;
        end else begin
            release a;
        end
        q = a;
    end
endmodule
module force_ranged_mod(
    input  logic       en,
    output logic [3:0] out
);
    logic [15:0] bus;
    always_comb begin
        bus = 16'h1234;
        if (en) begin
            force bus[3:0] = 4'hA;
        end else begin
            release bus[3:0];
        end
        out = bus[3:0];
    end
endmodule
module force_wire_mod(
    input  logic in,
    input  logic ctrl,
    output logic y
);
    logic w;
    always_comb begin
        w = in;
        if (ctrl) begin
            force w = 1'b0;
        end else begin
            release w;
        end
        y = w;
    end
endmodule
module force_task_mod(
    input  logic ctrl,
    output logic out
);
    logic temp;
    task automatic do_force(input logic enable);
        if (enable) begin
            force temp = 1'b1;
        end else begin
            release temp;
        end
    endtask
    always_comb begin
        do_force(ctrl);
        out = temp;
    end
endmodule
module force_class_mod(
    input  logic       clk,
    input  logic       en,
    output logic [7:0] data_out
);
    class dummy;
        rand logic [7:0] val;
        function new(input logic [7:0] v);
            val = v;
        endfunction
    endclass
    logic [7:0] data;
    logic       internal_toggle;
    always_ff @(posedge clk) begin
        internal_toggle <= ~internal_toggle;
    end
    always_comb begin
        dummy d;
        data = 8'h00;
        d = new(data);
        if (en) begin
            force data = d.val;
        end else begin
            release data;
        end
        data_out = data ^ {8{internal_toggle}};
    end
endmodule
module force_nested_mod(
    input  logic [1:0] sel,
    input  logic       en,
    output logic [7:0] odata
);
    logic [3:0][7:0] arr;
    always_comb begin
        if (en) begin
            force arr[sel] = 8'hFF;
        end else begin
            release arr[sel];
        end
        odata = arr[sel];
    end
endmodule
