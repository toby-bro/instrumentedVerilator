module param_static_cov #(
    parameter int WIDTH = 8,
    parameter logic [WIDTH-1:0] MASK = 'hAA
) (
    input  logic                     clk,
    input  logic [WIDTH-1:0]         din,
    output logic [WIDTH-1:0]         dout
);
    static logic [WIDTH-1:0] sreg = '0;
    always_ff @(posedge clk) begin
        sreg <= din ^ MASK;
    end
    assign dout = sreg;
    property p_match;
        @(posedge clk) (dout === din);
    endproperty
    cover property (p_match);
endmodule
module struct_func (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    typedef struct {
        logic [7:0]  a;
        logic [15:0] b;
    } my_u_struct;   
    function automatic logic [7:0] get_a (my_u_struct s);
        return s.a;
    endfunction
    function automatic logic [7:0] process (logic [7:0] value);
        my_u_struct loc;
        loc.a = value;
        loc.b = {value, value};
        return get_a(loc);   
    endfunction
    assign out_data = process(in_data);
endmodule
module class_mod (
    input  logic [7:0] data_in,
    output logic [31:0] data_out
);
    class adder_c;
        int inc;
        function new (int v = 1);
            inc = v;
        endfunction
        function int add (int x);
            return x + inc;   
        endfunction
    endclass
    adder_c c_inst;
    always_comb begin
        c_inst = new(5);               
        data_out = c_inst.add(data_in); 
    end
endmodule
module array_wide_mod (
    input  logic [31:0]       index,
    input  logic [127:0]      data_in,
    output logic [127:0]      data_out
);
    logic [127:0] mem [0:3];
    always_comb begin
        mem[index[1:0]] = data_in;   
        data_out        = mem[index[1:0]];
    end
endmodule
module event_var_mod (
    input  logic trigger,
    output logic flag
);
    event e;
    logic flag_reg = 1'b0;
    always_ff @(posedge trigger) begin
        -> e;           
    end
    always @(e) begin
        flag_reg <= 1'b1; 
    end
    assign flag = flag_reg;
endmodule
