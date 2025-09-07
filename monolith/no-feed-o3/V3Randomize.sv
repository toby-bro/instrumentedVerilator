module mod_random_basic(
    input  logic clk,
    output logic        out_bit
);
    class RBasic;
        rand bit [7:0]  a;
        rand bit [15:0] b;
        constraint c_basic {
            a < 8'd10;
            b inside {[16'd5:16'd20]};
        }
    endclass
    always_ff @(posedge clk) begin
        RBasic obj = new();
        void'(obj.randomize());
        out_bit <= obj.a[0];
    end
endmodule
module mod_random_inline(
    input  logic        clk,
    output logic [3:0]  out_val
);
    class RInline;
        rand bit [3:0] v;
    endclass
    always_ff @(posedge clk) begin
        RInline o = new();
        void'(o.randomize() with { v > 4'd5 && v < 4'd12; });
        out_val <= o.v;
    end
endmodule
module mod_rand_mode(
    input  logic in_sig,
    output logic out_sig
);
    class RMode;
        rand bit [7:0] x;
    endclass
    always_comb begin
        RMode e = new();
        e.rand_mode(0);          
        e.x.rand_mode(1);        
        void'(e.randomize());
        out_sig = in_sig ^ e.x[0];
    end
endmodule
module mod_constraint_mode(
    input  logic in_sig,
    output logic out_sig
);
    class CMode;
        rand bit y;
        constraint c1 { y == 1'b0; }
    endclass
    always_comb begin
        CMode f = new();
        f.constraint_mode(0);      
        f.c1.constraint_mode(1);   
        void'(f.randomize());
        out_sig = in_sig ^ f.y;
    end
endmodule
module mod_std_randomize(
    input  logic [3:0] din,
    output logic [3:0] dout
);
    always_comb begin
        logic [3:0] tmp;
        std::randomize(tmp) with { tmp inside {[4'd0 : 4'd15]}; };
        dout = tmp ^ din;
    end
endmodule
module mod_randcase(
    input  logic        clk,
    output logic [1:0]  sel
);
    always_ff @(posedge clk) begin
        randcase
            3: sel <= 2'b00;
            2: sel <= 2'b01;
            1: sel <= 2'b10;
        endcase
    end
endmodule
module mod_constraint_foreach(
    input  logic        clk,
    output logic [7:0]  sum_out
);
    class CArr;
        rand bit [7:0] arr [4];
        constraint c_fe {
            foreach (arr[i]) { arr[i] inside {[8'd0 : 8'd30]}; }
        }
    endclass
    always_ff @(posedge clk) begin
        CArr ac = new();
        void'(ac.randomize());
        sum_out <= ac.arr[0] + ac.arr[1] + ac.arr[2] + ac.arr[3];
    end
endmodule
module mod_struct_rand(
    input  logic clk,
    output logic [7:0] sum_out
);
    typedef struct packed {
        rand bit [3:0] a;
        rand bit [3:0] b;
    } pkt_t;
    class CStruct;
        rand pkt_t p;
    endclass
    always_ff @(posedge clk) begin
        CStruct s = new();
        void'(s.randomize());
        sum_out <= s.p.a + s.p.b;
    end
endmodule
module mod_queue_rand(
    input  logic clk,
    output logic [7:0] first_val
);
    class QRand;
        rand bit [7:0] q[$];
        constraint c_sz { q.size() == 3; }
    endclass
    always_ff @(posedge clk) begin
        QRand qo = new();
        void'(qo.randomize());
        first_val <= qo.q[0];
    end
endmodule
module mod_randc_enum(
    input  logic        in_bit,
    output logic [2:0]  out_state
);
    class CEnum;
        typedef enum logic [2:0] {IDLE=0, RUN=1, STOP=2} state_e;
        randc state_e st;
    endclass
    always_comb begin
        CEnum ce = new();
        void'(ce.randomize());
        out_state = ce.st ^ {2'b00,in_bit};
    end
endmodule
module mod_srandom_inheritance(
    input  logic        clk,
    input  logic [31:0] seed_in,
    output logic [3:0]  sum_out
);
    class BaseC;
        rand bit [3:0] a;
    endclass
    class DerC extends BaseC;
        rand bit [3:0] b;
    endclass
    always_ff @(posedge clk) begin
        DerC d = new();
        d.srandom(seed_in);
        void'(d.randomize());
        sum_out <= d.a + d.b;
    end
endmodule
module mod_dynamic_array(
    input  logic clk,
    output logic [7:0] dyn_sum
);
    class DynC;
        rand bit [7:0] da[];                    
        constraint c_da {
            da.size() == 2;
            foreach (da[i]) { da[i] inside {[8'd10:8'd20]}; }
        }
    endclass
    always_ff @(posedge clk) begin
        DynC dc = new();
        void'(dc.randomize());
        dyn_sum <= dc.da[0] + dc.da[1];
    end
endmodule
