module unique_if_mod
(
    input  logic [1:0] sel_i,
    output logic       res_o
);
    always_comb begin
        unique if (sel_i == 2'b00) begin
            res_o = 1'b0;
        end else if (sel_i == 2'b01) begin
            res_o = 1'b1;
        end else if (sel_i == 2'b10) begin
            res_o = 1'b0;
        end else begin
            res_o = 1'b1;
        end
    end
endmodule
module unique0_if_mod
(
    input  logic [1:0] sel_i,
    output logic       res_o
);
    always_comb begin
        unique0 if (sel_i == 2'b00) begin
            res_o = 1'b0;
        end else if (sel_i == 2'b01) begin
            res_o = 1'b1;
        end else begin
            res_o = 1'b0;
        end
    end
endmodule
module unique_case_mod
(
    input  logic [1:0] sel_i,
    output logic       res_o
);
    always_comb begin
        unique case (sel_i)
            2'b00: res_o = 1'b0;
            2'b01: res_o = 1'b1;
            default: res_o = 1'b0;
        endcase
    end
endmodule
module priority_case_mod
(
    input  logic [1:0] sel_i,
    output logic       res_o
);
    always_comb begin
        priority case (sel_i)
            2'b00: res_o = 1'b0;
            2'b01: res_o = 1'b1;
            default: res_o = 1'b0;
        endcase
    end
endmodule
module full_parallel_case_mod
(
    input  logic [1:0] sel_i,
    output logic       res_o
);
    always_comb begin
        (* full_case, parallel_case *) case (sel_i)
            2'b00: res_o = 1'b0;
            2'b01: res_o = 1'b1;
            default: res_o = 1'b0;
        endcase
    end
endmodule
module assert_property_mod
(
    input  logic clk,
    input  logic rst_n,
    input  logic a_i,
    input  logic b_i,
    output logic pass_o
);
    assign pass_o = a_i | b_i;
    property p1;
        disable iff (!rst_n)
        $past(a_i) |-> b_i;
    endproperty
    property p2;
        disable iff (!rst_n)
        a_i |-> ##1 b_i;
    endproperty
    assert  property (@(posedge clk) p1);
    cover   property (@(posedge clk) p2);
    restrict property (@(posedge clk) (a_i & b_i));
    always_ff @(posedge clk) begin
        assert (a_i != b_i);
    end
endmodule
module past_sampled_mod
(
    input  logic clk,
    input  logic data_i,
    output logic sampled_o
);
    assign sampled_o = data_i;
    property p_sampled;
        $sampled(data_i);
    endproperty
    cover property (@(posedge clk) p_sampled);
endmodule
module assert_control_mod
(
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    assign out_sig = in_sig;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            $assertoff;   
        end else begin
            $asserton;    
        end
    end
endmodule
