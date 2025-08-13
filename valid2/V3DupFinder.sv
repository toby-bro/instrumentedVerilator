//*********************************************************************
//*********************************************************************
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_arith
    #(parameter WIDTH = 8)
    (input  logic [WIDTH-1:0] in1,
     input  logic [WIDTH-1:0] in2,
     output logic [WIDTH-1:0] out1,
     output logic [WIDTH-1:0] out2);
    logic [WIDTH-1:0] temp1;
    logic [WIDTH-1:0] temp2;
    assign temp1 = (in1 + in2);                 
    assign temp2 = (in1 + in2);                 
    assign out1  = (temp1 * 2) + (temp1 * 2);   
    assign out2  = (temp2 * 2) - (temp2 * 2);   
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_if
    (input  logic a,
     input  logic b,
     output logic y);
    always_comb begin
        if (a & b)              
            y = 1'b1;
        else if (a & b)         
            y = 1'b1;
        else
            y = 1'b0;
    end
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_case
    (input  logic [1:0] sel,
     output logic [3:0] data);
    always_comb begin
        unique case (sel)
            2'd0: data = 4'hA;
            2'd1: data = 4'hB;
            2'd0: data = 4'hA;
            2'd1: data = 4'hB;
            default: data = 4'h0;
        endcase
    end
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_function
    (input  logic [7:0] in_val,
     output logic [7:0] out_f1,
     output logic [7:0] out_f2);
    function automatic logic [7:0] f_calc_1 (input logic [7:0] x);
        return (x ^ 8'hFF) + (x ^ 8'hFF);
    endfunction
    function automatic logic [7:0] f_calc_2 (input logic [7:0] x);
        return (x ^ 8'hFF) + (x ^ 8'hFF);
    endfunction
    assign out_f1 = f_calc_1(in_val);
    assign out_f2 = f_calc_2(in_val);
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_struct
    (input  logic clk,
     input  logic rst_n,
     input  logic [15:0] in_pay,
     output logic [15:0] out_pay);
    typedef struct packed {
        logic [7:0]  upper;
        logic [7:0]  lower;
    } payload_t;
    payload_t p1, p2;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            p1 <= '{upper:8'h0, lower:8'h0};
            p2 <= '{upper:8'h0, lower:8'h0};
        end
        else begin
            p1.upper <= in_pay[15:8];
            p1.lower <= in_pay[7:0];
            p2.upper <= in_pay[15:8];   
            p2.lower <= in_pay[7:0];    
        end
    end
    assign out_pay = {p2.upper, p2.lower};
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_generate
    (input  logic  ctrl,
     output logic [3:0] y);
    logic [3:0] internal0;
    logic [3:0] internal1;
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : G0
            assign internal0[i] = ctrl & 1'b1;
        end
        for (i = 0; i < 4; i++) begin : G1
            assign internal1[i] = ctrl & 1'b1;  
        end
    endgenerate
    assign y = internal0 | internal1;
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_class
    (input  logic [7:0] din,
     output logic [7:0] dout);
    class simple_c;
        function automatic logic [7:0] pass_thru (input logic [7:0] x);
            return (x);               
        endfunction
    endclass
    always_comb begin
        automatic simple_c c1 = new();
        automatic simple_c c2 = new();
        dout = c1.pass_thru(din) ^ c2.pass_thru(din);  
    end
endmodule
//---------------------------------------------------------------
//---------------------------------------------------------------
module dup_array
    (input  logic [3:0] in_arr,
     output logic [3:0] out_arr);
    wire duplicate0 = &in_arr[3:2];
    wire duplicate1 = &in_arr[3:2];   
    assign out_arr = {duplicate0, duplicate1, duplicate0, duplicate1};
endmodule
