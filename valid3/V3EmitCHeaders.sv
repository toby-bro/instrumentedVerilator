module subcell #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    always_comb out = in;
endmodule
module parent_with_cell (
    input  logic [7:0] a,
    output logic [7:0] y
);
    always_comb y = a;
endmodule
module enum_param_module #(
    parameter int CONST_VAL = 4,
    parameter bit FLAG = 1'b1
) (
    input  logic enable,
    output logic flag
);
    typedef enum logic [1:0] {
        IDLE = 2'd0,
        RUN  = 2'd1,
        DONE = 2'd2
    } state_e;
    state_e state;
    always_comb begin
        if (enable)
            state = RUN;
        else
            state = IDLE;
        flag = (state == RUN) ? FLAG : ~FLAG;
    end
endmodule
module packed_union_module (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_s;
    typedef union packed {
        logic  [15:0] whole;
        bytes_s       bytes;
    } data_u;
    data_u mydata;
    always_comb begin
        mydata.whole = in_data;
        if (mydata.bytes.hi[7])
            out_data = {8'h00, mydata.bytes.lo};
        else
            out_data = {8'h00, mydata.bytes.hi};
    end
endmodule
module rand_struct_module (
    input  logic       clk,
    input  logic [7:0] in_byte,
    output logic [7:0] o_byte
);
    typedef struct packed {
        logic [7:0] data_byte;
        logic [3:0] nibble;
    } rand_s;
    rand_s rs;
    always_ff @(posedge clk) begin
        rs.data_byte <= in_byte;
    end
    always_comb o_byte = rs.data_byte;
endmodule
module unpacked_struct_module (
    input  logic        sel,
    input  logic [31:0] data_in,
    output logic [31:0] data_out
);
    typedef struct {
        logic [15:0] lower;
        logic [15:0] upper;
    } word_s;
    word_s myword;
    always_comb begin
        myword.lower = data_in[15:0];
        myword.upper = data_in[31:16];
        if (sel)
            data_out = {myword.upper, myword.lower};
        else
            data_out = data_in;
    end
endmodule
module class_inst_module (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class MyClass;
        logic [7:0] data;
        function new();
            data = 8'h00;
        endfunction
        function void reset();
            data = 8'h00;
        endfunction
        function void update(input logic [7:0] val);
            data = val;
        endfunction
        function logic [7:0] get();
            return data;
        endfunction
    endclass
    MyClass obj;
    initial obj = new();
    always_ff @(posedge clk) begin
        if (rst)
            obj.reset();
        else
            obj.update(din);
    end
    always_comb dout = obj.get();
endmodule
