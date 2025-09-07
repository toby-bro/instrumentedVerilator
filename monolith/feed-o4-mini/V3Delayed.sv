module shadow_var_nba(
    input  logic        clk,
    input  logic [3:0]  in,
    output logic [3:0]  out
);
    logic [3:0] __Vdly__reg;
    always_ff @(posedge clk) begin
        __Vdly__reg <= in;
        out          <= __Vdly__reg;
    end
endmodule
module shadow_var_masked(
    input  logic        clk,
    input  logic [7:0]  in,
    input  logic [2:0]  sel,
    output logic [7:0]  out
);
    logic [7:0] __Vdly__data;
    logic [7:0] __VdlyMask__data;
    always_ff @(posedge clk) begin
        __Vdly__data     <= in;
        __VdlyMask__data <= 8'b0;
        out              <= (__Vdly__data & __VdlyMask__data)
                          | (in           & ~__VdlyMask__data);
    end
endmodule
module flag_shared(
    input  logic        clk,
    input  logic [7:0]  d_in,
    input  logic [1:0]  idx0,
    input  logic [1:0]  idx1,
    output logic [7:0]  d_out
);
    logic        __VdlySet_val;
    logic [7:0]  __VdlyVal_val;
    always_ff @(posedge clk) begin
        __VdlyVal_val <= d_in;
        __VdlySet_val <= 1'b1;
        if (__VdlySet_val) begin
            d_out <= __VdlyVal_val;
        end
    end
endmodule
module flag_unique(
    input  logic        clk,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic        __VdlySet_out;
    logic [7:0]  __VdlyVal_out;
    always_ff @(posedge clk) begin
        __VdlyVal_out <= in;
        __VdlySet_out <= 1'b1;
        if (__VdlySet_out) begin
            __VdlySet_out <= 1'b0;
            out           <= __VdlyVal_out;
        end
    end
endmodule
module value_queue_whole(
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] queue_w[$];
    always_ff @(posedge clk) begin
        queue_w.push_back(din);
    end
    always_ff @(posedge clk) begin
        if (queue_w.size() > 0) begin
            dout <= queue_w.pop_front();
        end
    end
endmodule
module value_queue_partial(
    input  logic        clk,
    input  logic [7:0]  src,
    input  logic [1:0]  sel,
    output logic [7:0]  dst
);
    logic [7:0] queue_p[$];
    logic [7:0] mask;
    always_ff @(posedge clk) begin
        queue_p.push_back(src);
    end
    always_ff @(posedge clk) begin
        if (queue_p.size() > 0) begin
            mask = 8'hFF >> sel;
            dst  <= queue_p.pop_front() & mask;
        end
    end
endmodule
module loops_and_selects(
    input  logic [7:0]  a,
    output logic [7:0]  sum_for,
    output logic [7:0]  sum_while
);
    logic [7:0] tmp1, tmp2;
    integer i, j;
    always_comb begin
        tmp1 = 0;
        for (i = 0; i < 8; i = i + 1)
            tmp1 = tmp1 + a[i];
        sum_for = tmp1;
        tmp2 = 0;
        j = 0;
        while (j < 8) begin
            tmp2[j] = a[j];
            j = j + 1;
        end
        sum_while = tmp2;
    end
endmodule
module branching_and_case(
    input  logic        x,
    input  logic        y,
    input  logic [1:0]  sel,
    input  logic [7:0]  din,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        if (x & y)
            out1 = din;
        else if (x)
            out1 = ~din;
        else
            out1 = 8'd0;
        case (sel)
            2'd0: out2 = din;
            2'd1: out2 = {din[3:0], din[7:4]};
            default: out2 = din ^ 8'hFF;
        endcase
    end
endmodule
module gen_example(
    input  logic [3:0] in,
    output logic [3:0] out
);
    genvar k;
    generate
        for (k = 0; k < 4; k = k + 1) begin : bit_loop
            assign out[k] = in[k];
        end
    endgenerate
endmodule
module event_trigger(
    input  logic        clk,
    input  logic [3:0]  in,
    output logic [3:0]  out
);
    event ev;
    always_ff @(posedge clk) begin
        -> ev;
    end
    always @(ev) begin
        out <= in;
    end
endmodule
module struct_and_array(
    input  logic [3:0]  i1,
    input  logic        i2,
    output logic [3:0]  o1,
    output logic        o2
);
    typedef struct packed {
        logic [3:0] data;
        logic       flag;
    } my_s;
    my_s arr [1:0];
    always_comb begin
        arr[0].data = i1;
        arr[0].flag = i2;
        o1 = arr[0].data;
        o2 = arr[0].flag;
    end
endmodule
module function_example(
    input  logic [7:0]  in,
    output logic [3:0]  out
);
    function automatic logic [3:0] lower_nibble(input logic [7:0] val);
        lower_nibble = val[3:0];
    endfunction
    always_comb begin
        out = lower_nibble(in);
    end
endmodule
module class_inst_example(
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    class Cnum;
        rand bit [7:0] v;
        function new(bit [7:0] iv); v = iv; endfunction
    endclass
    Cnum obj;
    always_ff @(posedge clk) begin
        obj = new(din);
        dout = obj.v;
    end
endmodule
module unpacked_array_nba(
    input  logic        clk,
    input  logic [3:0]  din,
    input  logic [1:0]  i0,
    input  logic [1:0]  i1,
    output logic [3:0]  dout
);
    logic [3:0] arr [0:1][0:1];
    always_ff @(posedge clk) begin
        arr[i0][i1] <= din;
    end
    always_ff @(posedge clk) begin
        dout <= arr[i0][i1];
    end
endmodule
module while_combination(
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic [7:0] tmp;
    integer j;
    always_comb begin
        tmp = 8'b0;
        j = 0;
        while (j < 8) begin
            tmp = tmp | (in << j);
            j = j + 1;
        end
        out = tmp;
    end
endmodule
module case_with_default(
    input  logic [2:0]  sel,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    always_comb begin
        case (sel)
            3'd0: dout = din;
            3'd4: dout = ~din;
            default: dout = 8'hAA;
        endcase
    end
endmodule
module nested_if(
    input  logic        a,
    input  logic        b,
    input  logic        c,
    output logic        y
);
    always_comb begin
        if (a) begin
            if (b) y = c;
            else   y = ~c;
        end else y = 1'b0;
    end
endmodule
module bit_and_part_select(
    input  logic [15:0] in,
    input  logic [3:0]  sel,
    output logic [7:0]  out_low,
    output logic [7:0]  out_high
);
    always_comb begin
        out_low  = in[sel +: 8];
        out_high = in[15 -: 8];
    end
endmodule
module latch_example(
    input  logic        en,
    input  logic [3:0]  in,
    output logic [3:0]  out
);
    always_latch begin
        if (en) out = in;
    end
endmodule
module do_while_example(
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic [7:0] tmp;
    integer k;
    always_comb begin
        tmp = 0;
        k = 0;
        do begin
            tmp = tmp + in[k];
            k = k + 1;
        end while (k < 8);
        out = tmp;
    end
endmodule
module generate_case(
    input  logic [1:0]  sel,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    genvar gi;
    logic [7:0] tbl [3:0];
    generate
        for (gi = 0; gi < 4; gi = gi + 1) begin : tbl_init
            assign tbl[gi] = gi;
        end
    endgenerate
    always_comb begin
        case (sel)
            2'd0: dout = tbl[0] + din;
            2'd1: dout = tbl[1] & din;
            default: dout = tbl[sel] ^ din;
        endcase
    end
endmodule
