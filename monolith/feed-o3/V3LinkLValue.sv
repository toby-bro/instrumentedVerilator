module cont_strength(
    input  wire in_sig,
    output wire out_sig
);
    assign (strong1, weak0) out_sig = in_sig;
endmodule
module force_release(
    input  logic       clk,
    input  logic       en,
    output logic [7:0] out_sig
);
    logic [7:0] reg_sig;
    assign out_sig = reg_sig;
    always_ff @(posedge clk) begin
        if (en)
            force reg_sig = 8'hFF;
        else
            release reg_sig;
    end
endmodule
module sel_inc(
    input  logic       clk,
    input  logic [3:0] din,
    output logic [3:0] out_sig
);
    logic [3:0] cnt;
    always_ff @(posedge clk) begin
        cnt <= cnt + din;
    end
    always_comb begin
        logic [3:0] tmp;
        tmp = cnt;
        out_sig = ++tmp;
    end
endmodule
module struct_member(
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } pair_t;
    pair_t s;
    always_comb begin
        s.a = in_sig;
        s.b = in_sig + 1;
        out_sig = s.b;
    end
endmodule
module cast_dynamic(
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    typedef enum logic [7:0] {A = 8'h00, B = 8'h01, C = 8'h02} my_e;
    always_comb begin
        automatic my_e e;
        if ($cast(e, in_sig))
            out_sig = e;
        else
            out_sig = 8'hFF;
    end
endmodule
module mem_plusargs(
    input  logic        in_dummy,
    output logic [7:0]  out_sig
);
    logic [7:0] mem [0:15];
    integer fd;
    logic [7:0] tmp;
    initial begin
        $readmemh("dummy.mem", mem);
        fd = $fopen("dummy.bin", "r");
        tmp = 0;
        $fread(fd, tmp);
        if ($test$plusargs("FOO")) begin end
        void'($value$plusargs("BAR=%d", mem[0]));
        $fclose(fd);
    end
    assign out_sig = mem[0];
endmodule
module rand_constraint(
    input  logic       in_dummy,
    output logic [7:0] out_sig
);
    class rand_c;
        rand bit [7:0] a;
        constraint c {
            a inside {[0:200]};
            a dist {[0:99] := 1, [100:200] := 2};
        }
    endclass
    always_comb begin
        automatic rand_c r;
        r = new();
        void'(r.randomize());
        out_sig = r.a;
    end
endmodule
module task_call(
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    task automatic inc(output logic [7:0] o, input logic [7:0] i);
        o = i + 8'h1;
    endtask
    always_comb begin
        inc(out_sig, in_sig);
    end
endmodule
module format_example(
    input  logic [7:0] in_sig,
    output logic [7:0] out_sig
);
    string str;
    always_comb begin
        str = $sformatf("Value=%0d", in_sig);
        out_sig = in_sig;
    end
endmodule
module part_select(
    input  logic [15:0] in_sig,
    input  logic [3:0]  idx,
    output logic [3:0]  out_sig
);
    assign out_sig = in_sig[idx +: 4];
endmodule
module file_gets_mod(
    input  logic       in_dummy,
    output logic [7:0] out_sig
);
    integer fd;
    string  line;
    initial begin
        fd = $fopen("dummy.txt", "r");
        line = "";
        $fgets(line, fd);
        $fclose(fd);
    end
    assign out_sig = 8'h0;
endmodule
module fscan_example(
    input  logic       in_dummy,
    output logic [7:0] out_sig
);
    integer fd;
    integer tmp_int;
    initial begin
        fd = $fopen("dummy.txt", "r");
        tmp_int = 0;
        $fscanf(fd, "%d", tmp_int);
        out_sig = tmp_int[7:0];
        $fclose(fd);
    end
endmodule
module fungetc_example(
    input  logic       in_dummy,
    output logic [7:0] out_sig
);
    integer fd;
    initial begin
        fd = $fopen("dummy.txt", "r");
        void'($fgetc(fd));
        $ungetc(8'h41, fd);
        $fclose(fd);
    end
    assign out_sig = 8'h0;
endmodule
module sscanf_example(
    input  logic       in_dummy,
    output logic [7:0] out_sig
);
    integer tmp;
    always_comb begin
        tmp = 0;
        $sscanf("42", "%d", tmp);
        out_sig = tmp[7:0];
    end
endmodule
module rand_syscall(
    input  logic [7:0] seed_in,
    output logic [7:0] rand_out
);
    logic [31:0] seed_reg;
    always_ff @(posedge seed_in[0]) begin
        seed_reg <= {24'h0, seed_in};
        rand_out <= $urandom(seed_reg)[7:0];
    end
endmodule
