module constraint_block_mod (
    input  logic        clk,
    output logic [7:0]  o
);
    class rand_block_cls;
        rand bit [7:0] a;
        rand bit [7:0] b;
        rand bit [7:0] c;
        constraint c_block {
            a inside { 2, 4, 6, 8 };
            b == a + 1;
            c dist { [0:3]  := 1,
                     [4:7]  := 2 };
        }
        function bit [7:0] value();
            return a;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        rand_block_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module implication_constraint_mod (
    input  logic       clk,
    output logic [7:0] o
);
    class imp_cls;
        rand bit  [3:0] mode;
        rand bit  [7:0] data;
        constraint imp_c {
            (mode == 4'd0) -> data inside {8'h00, 8'hFF};
            (mode == 4'd1) -> data == 8'hAA;
        }
        function bit [7:0] value();
            return data;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        imp_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module conditional_constraint_mod (
    input  logic       clk,
    output logic [7:0] o
);
    class cond_cls;
        rand bit        flag;
        rand bit [7:0]  x;
        rand bit [7:0]  y;
        constraint cond_c {
            if (flag)    x == y;
            else         x != y;
        }
        function bit [7:0] value();
            return x;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        cond_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module uniqueness_constraint_mod (
    input  logic       clk,
    output logic [7:0] o
);
    class uniq_cls;
        rand bit [7:0] u1, u2, u3;
        constraint uq_c { unique { u1, u2, u3 }; }
        function bit [7:0] value();
            return u1;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        uniq_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module disable_soft_constraint_mod (
    input  logic       clk,
    output logic [7:0] o
);
    class soft_cls;
        rand bit [7:0] s;
        constraint soft_default { soft s == 8'h55; }
        constraint disable_c    { disable soft s;   }
        function bit [7:0] value();
            return s;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        soft_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module solve_before_constraint_mod (
    input  logic      clk,
    output logic [3:0] o
);
    class solve_cls;
        rand bit [3:0] a;
        rand bit [3:0] b;
        constraint sv_c { solve a before b; }
        function bit [3:0] value();
            return a;
        endfunction
    endclass
    always_ff @(posedge clk) begin
        solve_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
module foreach_constraint_mod (
    input  logic       clk,
    output logic [7:0] o
);
    class foreach_cls;
        rand bit [7:0] arr [4];
        constraint fc {
            foreach (arr[i]) arr[i] == i;
        }
        function bit [7:0] value();
            return arr[0];
        endfunction
    endclass
    always_ff @(posedge clk) begin
        foreach_cls obj = new();
        if (obj.randomize())
            o <= obj.value();
        else
            o <= '0;
    end
endmodule
