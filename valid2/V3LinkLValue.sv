module strength_alias_mod(
    input  wire [7:0] in,
    output wire [7:0] out,
    output wire [7:0] alias_out
);
    wire [7:0] w;
    assign w = in;
    assign (strong1, weak0) out = w;
    alias alias_out = w;
endmodule
module force_release_mod(
    input  logic clk,
    input  logic in,
    output logic q
);
    always_ff @(posedge clk) q <= in;
    always_comb begin
        force q = in;
        release q;
    end
endmodule
module cast_event_mod(
    input  logic [31:0] in,
    output logic [31:0] out
);
    event ev;
    bit success;
    always_comb begin
        success = $cast(out, in);
        -> ev;
    end
endmodule
module file_ops_mod(
    input  logic [31:0] in,
    output logic [31:0] out
);
    int    fd;
    string s;
    int    code;
    int    ret;
    logic [31:0] mem [0:255];
    always_comb begin
        ret  = $ferror(fd, code);
        ret  = $fgets(s, fd);
        ret  = $fscanf(fd, "%0d", out);
        ret  = $sscanf(s, "%0d", out);
        $sformat(s, "val=%0d", in);
        code = $test$plusargs("TEST_ARG");
        ret  = $value$plusargs("VAL=%d", out);
        ret  = $ungetc(in[7:0], fd);
        ret  = $fread(mem, fd);
    end
endmodule
module random_constraint_mod(
    input  logic clk,
    output logic [7:0] out
);
    class rand_class;
        rand bit [7:0] r;
        constraint c { r dist {8'h00:/1, [8'h01:8'h0A]:/2}; }
    endclass
    rand_class obj;
    always_ff @(posedge clk) begin
        obj = new();
        if (obj.randomize()) out <= obj.r;
    end
endmodule
module prepost_sel_mod(
    input  logic [7:0] in,
    output logic [7:0] out
);
    logic [7:0] a;
    int cnt;
    always_comb begin
        a = in;
        out = {4'b0, a[3+:4]};
        cnt = ++cnt;
        cnt--;
    end
endmodule
module member_sel_task_mod(
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef struct packed {logic [3:0] lo; logic [3:0] hi;} s_t;
    s_t st;
    task automatic packTask(input s_t src, output logic [7:0] dest);
        dest = {src.hi, src.lo};
    endtask
    always_comb begin
        st.lo = in[3:0];
        st.hi = in[7:4];
        packTask(st, out);
    end
endmodule
module child(
    input  logic up,
    output logic o
);
    assign o = up;
endmodule
module hier_mod(
    input  logic i,
    output logic o
);
    child c_inst (.up(i), .o(o));
endmodule
