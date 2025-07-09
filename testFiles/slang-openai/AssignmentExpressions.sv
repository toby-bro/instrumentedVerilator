module basic_assign (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] reg_data;
    always_ff @(posedge clk) begin
        reg_data <= din;           
        reg_data += 8'h1;          
    end
    assign dout = reg_data;
endmodule
module struct_pat_mod (
    input  logic [3:0] in1,
    input  logic [3:0] in2,
    output logic [7:0] out
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } p_s_t;
    p_s_t s;
    always_comb begin
        s = '{in1, in2};   
    end
    assign out = s;
endmodule
module array_pat_mod (
    input  logic [7:0] val,
    output logic [31:0] out
);
    logic [7:0] arr[0:3];
    always_comb begin
        arr = '{4{val}};          
    end
    assign out = {arr[3], arr[2], arr[1], arr[0]};
endmodule
module dyn_array_mod (
    input  logic [7:0] val,
    output logic [7:0] first_elem
);
`ifndef VERILATOR
    int dyn[];
    always_comb begin
        dyn       = new[4];
        dyn[0]    = val;
        first_elem = (dyn.size() != 0) ? dyn[0] : 8'h00;
    end
`else
    assign first_elem = val;
`endif
endmodule
module class_new_mod (
    input  logic [7:0] val,
    output logic [7:0] rv
);
`ifndef VERILATOR
    class myC;
        bit [7:0] data;
        function new(bit [7:0] d = 0);
            data = d;
        endfunction
        function bit [7:0] get();
            return data;
        endfunction
    endclass
    myC obj;
    always_comb begin
        obj = new(val);
        rv  = obj.get();
    end
`else
    assign rv = val;
`endif
endmodule
module struct_named_pat_mod (
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    output logic [7:0] out_s
);
`ifndef VERILATOR
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } st_t;
    st_t s;
    always_comb begin
        s = '{default:4'h0, a:in_a, b:in_b};  
    end
    assign out_s = s;
`else
    assign out_s = {in_a, in_b};
`endif
endmodule
