module slice_assign_basic (
    input  logic [7:0] in_bus  [0:3],
    output logic [7:0] out_bus [0:3]
);
    assign out_bus = in_bus;
endmodule
module slice_assign_desc (
    input  logic                         en,
    input  logic [7:0] in_bus  [0:3],    
    output logic [7:0] out_bus [3:0]     
);
    always_comb begin
        if (en) begin
            out_bus = in_bus;            
        end
    end
endmodule
module slice_assign_cond (
    input  logic                         sel,
    input  logic [7:0] in0 [0:3],
    input  logic [7:0] in1 [0:3],
    output logic [7:0] out_bus [0:3]
);
    assign out_bus = sel ? in0 : in1;
endmodule
module slice_assign_literal (
    input  logic                         stub_in,
    output logic [7:0] out_bus [0:3]
);
    assign out_bus = '{8'h01, 8'h02, 8'h03, 8'h04};
endmodule
module slice_equality (
    input  logic [7:0] in0 [0:3],
    input  logic [7:0] in1 [0:3],
    output logic                       eq
);
    assign eq = (in0 == in1);
endmodule
module slice_inequality (
    input  logic [7:0] in0 [0:3],
    input  logic [7:0] in1 [0:3],
    output logic                       neq
);
    assign neq = (in0 != in1);
endmodule
module slice_eqcase (
    input  logic [7:0] in0 [0:3],
    input  logic [7:0] in1 [0:3],
    output logic                       eq_case
);
    assign eq_case = (in0 === in1);
endmodule
module slice_neqcase (
    input  logic [7:0] in0 [0:3],
    input  logic [7:0] in1 [0:3],
    output logic                       neq_case
);
    assign neq_case = (in0 !== in1);
endmodule
module slice_dynamic_array (
    input  logic [1:0] idx,
    output logic [15:0] elem
);
    function automatic [15:0] get_elem (input logic [1:0] i);
        int dyn_arr[] = '{16'h1, 16'h2, 16'h3, 16'h4};   
        get_elem = dyn_arr[i];
    endfunction
    assign elem = get_elem(idx);
endmodule
module slice_queue (
    input  logic [1:0] idx,
    output logic [15:0] elem
);
    function automatic [15:0] get_elem_q (input logic [1:0] i);
        int q[$] = '{16'h9, 16'hA, 16'hB, 16'hC};        
        get_elem_q = q[i];
    endfunction
    assign elem = get_elem_q(idx);
endmodule
module slice_struct (
    input  logic                stub_in,
    output logic [7:0]          sum
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } s_t;
    s_t s_var = '{a:4'hF, b:4'hE};
    assign sum = {4'd0, s_var.a} + {4'd0, s_var.b};
endmodule
module slice_subsel (
    input  logic [7:0] in_bus [0:3],
    output logic [3:0] high_nibble
);
    assign high_nibble = in_bus[2][7:4];
endmodule
