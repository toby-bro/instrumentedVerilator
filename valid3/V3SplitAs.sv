module split_basic(
    input  logic clk,
    input  logic in,
    output logic out
);
    logic reg1;
    logic reg2;
    always_ff @(posedge clk) begin
        reg1 /* isolate_assignments */ <= in;
        reg2 <= ~reg1;
        out  <= reg2;
    end
endmodule
module split_nested(
    input  logic       clk,
    input  logic [7:0] data_in,
    input  logic       enable,
    output logic [7:0] data_out
);
    logic [7:0] acc;
    logic [7:0] temp;
    always_ff @(posedge clk) begin
        if (enable) begin
            if (data_in[0]) begin
                acc /* isolate_assignments */ <= acc + data_in;
            end else begin
                acc /* isolate_assignments */ <= acc - data_in;
            end
            temp <= acc ^ data_in;
        end
        data_out <= temp;
    end
endmodule
module split_func_ref(
    input  logic       clk,
    input  logic [3:0] din,
    output logic [3:0] out
);
    logic [3:0] counter;
    function automatic logic [3:0] inc(input logic [3:0] v);
        inc = v + 1;
    endfunction
    always_ff @(posedge clk) begin
        counter /* isolate_assignments */ <= inc(counter);
        out <= counter ^ din;
    end
endmodule
module split_loop(
    input  logic clk,
    input  logic start,
    output logic done
);
    logic [7:0] mem [0:7];
    logic [3:0] progress;
    always_ff @(posedge clk) begin
        if (start) begin
            for (int i = 0; i < 8; i++) begin
                mem[i] /* isolate_assignments */ <= mem[i] + {5'b0, i[2:0]};
            end
            progress <= 4'd8;
        end
        done <= start & (progress == 4'd8) & mem[0][0];
    end
endmodule
module split_two_vars(
    input  logic        clk,
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] y
);
    logic [15:0] x;
    logic [15:0] z;
    always_ff @(posedge clk) begin
        x /* isolate_assignments */ <= a + b;
        z /* isolate_assignments */ <= a - b;
        y <= x ^ z;
    end
endmodule
module split_case(
    input  logic       clk,
    input  logic [1:0] sel,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] value;
    always_ff @(posedge clk) begin
        case (sel)
            2'b00: value /* isolate_assignments */ <= din;
            2'b01: value /* isolate_assignments */ <= ~din;
            2'b10: value /* isolate_assignments */ <= din + 8'd1;
            default: value /* isolate_assignments */ <= 8'h00;
        endcase
        dout <= value;
    end
endmodule
module split_multiple_always(
    input  logic       clk,
    input  logic [3:0] in1,
    input  logic [3:0] in2,
    output logic [3:0] out
);
    logic [3:0] shared;
    always_ff @(posedge clk) begin
        shared /* isolate_assignments */ <= in1;
    end
    always_ff @(posedge clk) begin
        out <= shared + in2;
    end
endmodule
module split_comb(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
    logic [7:0] sum;
    always_comb begin
        sum /* isolate_assignments */ = a + b;
        y = sum ^ b;
    end
endmodule
