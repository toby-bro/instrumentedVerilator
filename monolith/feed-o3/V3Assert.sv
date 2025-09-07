module assert_ctrl_demo(
    input  logic        clk,
    input  logic        rst_n,
    input  logic [3:0]  in_sig,
    output logic        out_sig
);
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_sig <= 1'b0;
            $asserton;
        end else begin
            out_sig <= ^in_sig;
            if (&in_sig) begin
                $assertoff;
            end
        end
    end
endmodule
module unique_if_demo#(
    parameter int WIDTH = 2
)(
    input  logic                clk,
    input  logic [WIDTH-1:0]    sel,
    input  logic [7:0]          data_in,
    output logic [7:0]          data_out
);
    always_ff @(posedge clk) begin
        unique if (sel == 2'd0)       data_out <= data_in + 8'd1;
        else if (sel == 2'd1)         data_out <= data_in - 8'd1;
        else if (sel == 2'd2)         data_out <= data_in ^ 8'hAA;
    end
endmodule
module priority_case_demo(
    input  logic       clk,
    input  logic [1:0] sel,
    input  logic [7:0] d,
    output logic [7:0] q
);
    always_ff @(posedge clk) begin
        (* full_case, parallel_case *)
        priority case (sel)
            2'd0:    q <= d;
            2'd1:    q <= ~d;
            default: q <= 8'hFF;
        endcase
    end
endmodule
module unique0_case_demo(
    input  logic       clk,
    input  logic [1:0] sel,
    output logic [1:0] out_code
);
    always_ff @(posedge clk) begin
        unique0 case (sel)
            2'd0: out_code <= 2'd1;
            2'd1: out_code <= 2'd2;
        endcase
    end
endmodule
module past_assert_demo(
    input  logic clk,
    input  logic rst,
    input  logic signal_in,
    output logic signal_out
);
    assign signal_out = signal_in;
    property hold_high;
        @(posedge clk) disable iff (rst) $past(signal_in) |-> signal_in;
    endproperty
    assert property (hold_high);
    cover property (@(posedge clk) signal_in && !$past(signal_in));
endmodule
module immediate_assert_demo(
    input  logic       clk,
    input  logic       enable,
    input  logic [3:0] value,
    output logic       flag
);
    always_ff @(posedge clk) begin
        flag <= enable & (value == 4'hA);
        assert (value != 4'hF) else begin end
        assume (enable == 1'b0 || flag);
        cover (flag);
    end
endmodule
