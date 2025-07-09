module unique_if_mod (
    input  logic        sel,
    input  logic [2:0]  in_bus,
    output logic        out_signal
);
    always_comb begin
`ifdef VERILATOR
        if (sel) begin
            out_signal = in_bus[0];
        end
        else if (in_bus[2]) begin
            out_signal = in_bus[1];
        end
        else begin
            out_signal = in_bus[2];
        end
`else
        unique if (sel) begin
            out_signal = in_bus[0];
        end
        else if (in_bus[2]) begin
            out_signal = in_bus[1];
        end
        else begin
            out_signal = in_bus[2];
        end
`endif
    end
endmodule
module priority_if_mod (
    input  logic [3:0] a,
    output logic       result
);
    always_comb begin
`ifdef VERILATOR
        if (a[3]) begin
            result = 1'b1;
        end
        else if (a[2]) begin
            result = 1'b0;
        end
        else begin
            result = 1'b1;
        end
`else
        priority if (a[3]) begin
            result = 1'b1;
        end
        else if (a[2]) begin
            result = 1'b0;
        end
        else begin
            result = 1'b1;
        end
`endif
    end
endmodule
module case_unique_mod (
    input  logic [3:0] sel,
    output logic [1:0] out_code
);
    always_comb begin
`ifdef VERILATOR
        case (sel)
            4'd0   : out_code = 2'd0;
            4'd1   : out_code = 2'd1;
            4'd2   : out_code = 2'd2;
            default: out_code = 2'd3;
        endcase
`else
        unique case (sel)
            4'd0   : out_code = 2'd0;
            4'd1   : out_code = 2'd1;
            4'd2   : out_code = 2'd2;
            default: out_code = 2'd3;
        endcase
`endif
    end
endmodule
module case_inside_mod (
    input  logic [3:0] val,
    output logic [1:0] category
);
    always_comb begin
        unique case (val) inside
            [4'd0:4'd3]: category = 2'd0;
            [4'd4:4'd7]: category = 2'd1;
            default    : category = 2'd2;
        endcase
    end
endmodule
module unique0_casex_mod (
    input  logic [3:0] bus,
    output logic [1:0] code
);
    always_comb begin
`ifdef VERILATOR
        casex (bus)
            4'b1???: code = 2'd0;
            4'b01??: code = 2'd1;
            default: code = 2'd3;
        endcase
`else
        unique0 casex (bus)
            4'b1???: code = 2'd0;
            4'b01??: code = 2'd1;
            default: code = 2'd3;
        endcase
`endif
    end
endmodule
module pattern_case_mod (
    input  logic [3:0] data,
    output logic       flag
);
    always_comb begin
`ifdef VERILATOR
        unique casez (data)
            4'b1?0?: flag = 1'b1;
            default: flag = 1'b0;
        endcase
`else
        priority case (data) matches
            4'b1?0?: flag = 1'b1;
            default: flag = 1'b0;
        endcase
`endif
    end
endmodule
module matches_if_mod (
    input  logic [3:0] data,
    output logic       matched
);
    always_comb begin
`ifdef VERILATOR
        matched = (data[3:2] == 2'b10);
`else
        if (data matches (4'b1?0?)) begin
            matched = 1'b1;
        end
        else begin
            matched = 1'b0;
        end
`endif
    end
endmodule
