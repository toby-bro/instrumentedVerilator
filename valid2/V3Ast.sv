typedef struct packed {logic [3:0] upper; logic [7:0] lower;} spack_t;
typedef union packed {
    logic [7:0] raw;
    struct packed {logic [3:0] low; logic [3:0] high;} halves;
} upack_t;
typedef enum logic [1:0] {S_IDLE=2'b00, S_RUN=2'b01, S_STOP=2'b10, S_ERR=2'b11} state_e;
module arith_ops #(
    parameter int WA = 8,
    parameter int WB = 16
) (
    input  logic signed [WA-1:0] a,
    input  logic signed [WB-1:0] b,
    output logic signed [WB-1:0] y
);
    localparam int CONST_NEG = -5;
    assign y = ((b + {{(WB-WA){a[WA-1]}}, a}) - CONST_NEG) >>> 1;
endmodule
module struct_feature (
    input  logic [11:0] in_data,
    output spack_t      out_struct
);
    always_comb begin
        out_struct = spack_t'(in_data);
    end
endmodule
module union_feature (
    input  logic  [7:0] din,
    output upack_t      uout
);
    always_comb begin
        uout = upack_t'(din);
    end
endmodule
module enum_cast (
    input  logic  [1:0] ctrl,
    output state_e      state
);
    always_comb begin
        state = state_e'(ctrl);
    end
endmodule
module queue_feature (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    function automatic logic [7:0] process(input logic [7:0] d);
        logic [7:0] q[$];
        q.push_back(d);
        return q.pop_front();
    endfunction
    assign dout = process(din);
endmodule
module class_feature (
    input  logic [31:0] din,
    output logic [31:0] dout
);
    class base_c;
        virtual function void set(int d); endfunction
        virtual function int  get(); return 0; endfunction
    endclass
    class child_c extends base_c;
        int data;
        function void set(int d); data = d; endfunction
        function int  get(); return data; endfunction
    endclass
    child_c h;
    always_comb begin
        h = new();
        h.set(din);
        dout = h.get();
    end
endmodule
module stream_concat (
    input  logic  [7:0] din,
    output logic [63:0] dout
);
    assign dout = {<<8{din}};
endmodule
module array_feature #(
    parameter int W = 4
) (
    input  logic [W-1:0] din0,
    input  logic [W-1:0] din1,
    output logic [W-1:0] dout
);
    logic [W-1:0] packed_arr [2];
    always_comb begin
        packed_arr[0] = din0;
        packed_arr[1] = din1;
        dout = packed_arr[0] ^ packed_arr[1];
    end
endmodule
