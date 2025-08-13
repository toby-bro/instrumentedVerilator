module m_feat1 (input logic clk, input logic [3:0] din, output logic [3:0] dout);
    typedef struct packed {
        logic [3:0] a;
        union packed {
            logic [3:0] u;
            struct packed {
                logic [1:0] x;
                logic [1:0] y;
            } s;
        } u1;
    } my_packed_t;
    my_packed_t static_instance;
    interface class compar;
        pure virtual function bit cmp(int a, int b);
    endclass
    virtual class base_c;
        typedef struct packed { logic [7:0] p; } pub_t;
        int data;
        task automatic write(int v); data = v; endtask
        pure virtual function int get();
    endclass
    class imp_c extends base_c implements compar;
        virtual function int get(); return data; endfunction
        virtual function bit cmp(int a, int b); return (a == b); endfunction
    endclass
    imp_c c_h;
    covergroup cg @(posedge clk);
        cp : coverpoint din;
    endgroup
    cg cg_inst;
    initial begin
        c_h = new();
        cg_inst = new();
        c_h.write(0);
    end
    always_ff @(posedge clk) begin
        dout <= din;
    end
endmodule
module m_feat2 (input logic clk, input logic [7:0] v_in, output logic [7:0] v_out);
    int counter;
    task incr(); counter++; endtask
    initial begin
        counter = 0;
    end
    always_ff @(posedge clk) begin
        incr();
        v_out <= v_in ^ counter[7:0];
    end
endmodule
module m_feat3 (input logic [1:0] sel, input logic [15:0] datain, output logic [15:0] dataout);
    typedef union packed {
        logic [15:0] wide;
        struct packed {
            logic [7:0] low;
            logic [7:0] high;
        } parts;
    } my_union_t;
    my_union_t u_in, u_out;
    always_comb begin
        u_in.wide = datain;
        if (sel == 2'd0) begin
            u_out.parts.low  = u_in.parts.high;
            u_out.parts.high = u_in.parts.low;
        end else begin
            u_out.wide = u_in.wide;
        end
        dataout = u_out.wide;
    end
endmodule
module m_feat4 #(parameter int WIDTH = 8) (input logic [WIDTH-1:0] a, output logic [WIDTH-1:0] y);
    logic [WIDTH-1:0] reg_r;
    always_comb begin
        reg_r = a;
    end
    assign y = reg_r;
endmodule
