typedef struct packed { logic a; logic [1:0] b; } mystr_t;
typedef struct { logic x; logic y; } mem_t;
module CloneAndSel_test #(parameter N = 4) (
    input  logic [1:0]         idx,
    input  logic [7:0]         data [0:N-1],
    output logic [7:0]         out_element
);
    assign out_element = data[idx];
endmodule
module SliceSel_test (
    input  logic [7:0]         data      [0:7],
    output logic [7:0]         slice_arr [4:7]
);
    assign slice_arr = data[4:7];
endmodule
module AssignDescending_test (
    input  logic [7:0]         arr_asc  [0:3],
    output logic [7:0]         arr_desc [3:0]
);
    integer i;
    always_comb begin
        for (i = 0; i < 4; i = i + 1)
            arr_desc[i] = arr_asc[i];
    end
endmodule
module InitArray_test (
    input  logic               enb,
    output logic [7:0]         arr [0:2]
);
    assign arr = '{8'hA1, 8'hB2, 8'hC3};
endmodule
module ConsPackStruct_test (
    input  logic [3:0]         in0,
    input  logic [3:0]         in1,
    output struct packed { logic [3:0] a; logic [3:0] b; } pack_out
);
    assign pack_out = '{a: in0, b: in1};
endmodule
module PackedToArray_test (
    input  logic [7:0]         in_vec,
    output logic [7:0]         arr_out [0:0]
);
    assign arr_out[0] = in_vec;
endmodule
module ConsDynArray_test (
    input  logic [7:0]         in0,
    input  logic [7:0]         in1,
    input  logic [7:0]         in2,
    input  logic [7:0]         in3,
    output logic [7:0]         out0
);
    logic [7:0] dyn_arr [];
    always_comb begin
        dyn_arr = new[4];
        dyn_arr[0] = in0;
        dyn_arr[1] = in1;
        dyn_arr[2] = in2;
        dyn_arr[3] = in3;
        out0 = dyn_arr[2];
    end
endmodule
module ConsQueue_test (
    input  logic [7:0]         in0,
    input  logic [7:0]         in1,
    input  logic [7:0]         in2,
    input  logic [7:0]         in3,
    output logic [7:0]         out0
);
    logic [7:0] que_q [$];
    always_comb begin
        que_q = {};
        que_q.push_back(in0);
        que_q.push_back(in1);
        que_q.push_back(in2);
        que_q.push_back(in3);
        out0 = que_q.pop_front();
    end
endmodule
module EqExpansion_test (
    input  logic [7:0]         arr1 [0:3],
    input  logic [7:0]         arr2 [0:3],
    output logic               eq_out
);
    assign eq_out = (arr1 == arr2);
endmodule
module NeqExpansion_test (
    input  logic [7:0]         arr1 [0:3],
    input  logic [7:0]         arr2 [0:3],
    output logic               neq_out
);
    assign neq_out = (arr1 != arr2);
endmodule
module EqCaseExpansion_test (
    input  logic [7:0]         arr1 [0:3],
    input  logic [7:0]         arr2 [0:3],
    output logic               eqcase_out
);
    assign eqcase_out = (arr1 === arr2);
endmodule
module NeqCaseExpansion_test (
    input  logic [7:0]         arr1 [0:3],
    input  logic [7:0]         arr2 [0:3],
    output logic               neqcase_out
);
    assign neqcase_out = (arr1 !== arr2);
endmodule
module VarRef_test (
    input  logic [15:0]        a,
    output logic [15:0]        b
);
    assign b = a;
endmodule
module StructSel_test (
    input  mystr_t             in_str [0:1],
    output logic               out_a,
    output logic [1:0]         out_b
);
    assign out_a = in_str[1].a;
    assign out_b = in_str[0].b;
endmodule
module MemberSel_test (
    input  logic [1:0]         idx_in,
    output logic               sel_x_out
);
    mem_t arr_mem [0:1];
    always_comb begin
        sel_x_out = arr_mem[idx_in].x;
    end
endmodule
module PackedSlice_test (
    input  logic [15:0]        wide_in,
    output logic [7:0]         part_out
);
    assign part_out = wide_in[7:0];
endmodule
