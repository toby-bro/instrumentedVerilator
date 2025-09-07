module m_enum(input  logic [3:0] in,
              output logic       out);
    typedef enum logic [1:0] {
        E0 = 2'd0,
        E1 = 2'd1,
        E2 = 2'd2,
        E3 = 2'd3
    } e_t;
    e_t state;
    always_comb begin
        state = e_t'(in[1:0]);          
        out   = (state == E3);
    end
endmodule
module m_struct(input  logic [7:0] in,
                output logic [7:0] out);
    typedef struct packed {
        logic [3:0] high;
        logic [3:0] low;
    } s_t;
    s_t st;
    always_comb begin
        st  = '{high: in[7:4], low: in[3:0]};
        out = {st.high, st.low};        
    end
endmodule
module m_union(input  logic [15:0] in,
               output logic [15:0] out);
    typedef union packed {
        logic [15:0] whole;
        struct packed {
            logic [7:0] lsb;
            logic [7:0] msb;
        } bytes;
    } u_t;
    u_t u;
    always_comb begin
        u.whole = in;
        out     = {u.bytes.msb, u.bytes.lsb}; 
    end
endmodule
module m_class(input  logic [3:0] in,
               output logic [3:0] out);
    class base;
        function automatic int foo(int a);
            return a + 1;
        endfunction
    endclass
    class derived extends base;
        rand int r;
        constraint c { r inside {[0:15]}; }
        function automatic int foo(int a);
            return super.foo(a) + 1;
        endfunction
    endclass
    derived d;          
    int     res;
    always_comb begin
        d   = new();    
        res = d.foo(in);
        out = res[3:0];
    end
endmodule
module m_param_type #(parameter type PT = logic [7:0])
                     (input  logic [7:0] in,
                      output var PT      out);
    PT local_var;
    always_comb begin
        local_var = PT'(in);    
        out       = local_var;
    end
endmodule
module m_task(input  logic [7:0] in,
              output logic [7:0] out);
    task automatic inc(input  logic [7:0] a,
                       output logic [7:0] b);
        b = a + 8'h1;
    endtask
    function automatic logic [7:0] wrapper(logic [7:0] v);
        logic [7:0] temp;
        inc(v, temp);           
        return temp;
    endfunction
    always_comb begin
        out = wrapper(in);      
    end
endmodule
module m_assigns(input  logic clk,
                 input  logic d,
                 output logic q);
    logic q_int;
    assign q = q_int;           
    always_ff @(posedge clk) begin
        q_int <= d;             
    end
endmodule
module m_cast(input  logic [7:0]  in,
              output logic [15:0] out);
    always_comb begin
        out = shortint'(in);    
    end
endmodule
