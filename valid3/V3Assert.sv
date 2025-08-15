module unique_if_mod(input  logic [1:0] sel,
                     output logic       y);
    always_comb
        unique if (sel == 2'b00)  y = 1'b0;
        else if (sel == 2'b01)    y = 1'b1;
        else if (sel == 2'b10)    y = 1'b0;
        else                      y = 1'b1;
endmodule
module unique0_if_mod(input  logic [1:0] sel,
                      output logic       y);
    always_comb
        unique0 if (sel == 2'b00) y = 1'b0;
        else if (sel == 2'b01)    y = 1'b1;
        else if (sel == 2'b10)    y = 1'b0;
        else                      y = 1'b1;
endmodule
module unique_case_mod(input  logic [1:0] sel,
                       output logic       y);
    always_comb begin
        unique case (sel)
            2'b00 : y = 1'b0;
            2'b01 : y = 1'b1;
            2'b10 : y = 1'b0;
            default: y = 1'b1;
        endcase
    end
endmodule
module priority_case_mod(input  logic [1:0] sel,
                         output logic       y);
    always_comb begin
        priority case (sel)
            2'b00 : y = 1'b0;
            2'b01 : y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module past_assert_mod(input  logic clk,
                       input  logic rst_n,
                       input  logic a,
                       output logic y);
    property p_past;
        @(posedge clk) disable iff (!rst_n) a |=> $past(a);
    endproperty
    assert property (p_past);
    always_ff @(posedge clk) begin
        if (!rst_n) y <= 1'b0;
        else        y <= a;
    end
endmodule
module sampled_mod(input  logic clk,
                   input  logic d,
                   output logic q);
    property p_sampled;
        @(posedge clk) (d == $sampled(d));
    endproperty
    assume property (p_sampled);
    always_ff @(posedge clk) q <= d;
endmodule
module cover_restrict_mod(input  logic clk,
                          input  logic in,
                          output logic out);
    property p_always_high;
        @(posedge clk) in;
    endproperty
    cover   property (p_always_high);
    restrict property (p_always_high);
    assign out = in;
endmodule
module assert_ctl_mod(input  logic clk,
                      input  logic a,
                      output logic y);
    always_ff @(posedge clk) begin
        $asserton;
        y <= a;
        $assertoff;
    end
endmodule
module monitoroff_mod(input  logic clk,
                      input  logic a,
                      output logic y);
    always_ff @(posedge clk) begin
        $monitoroff;
        y <= a;
    end
endmodule
