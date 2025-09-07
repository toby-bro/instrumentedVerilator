/////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
//=========================================================
//=========================================================
module m_basic_types #(parameter WIDTH = 8)
(
    input  logic [WIDTH-1:0] i_data,
    output logic [WIDTH-1:0] o_data
);
    typedef enum logic [1:0] { RED=2'b00, GREEN=2'b01, BLUE=2'b10 } color_e;
    typedef struct packed {
        color_e        hue;
        logic [WIDTH-1:0] payload;
    } pkt_t;
    logic [WIDTH-1:0] p_arr [0:3];
    pkt_t u_arr [0:1];
    localparam logic [WIDTH-1:0] CONST_VAL = WIDTH'(8'hA5);
    always_comb begin
        p_arr[0]          = i_data;
        p_arr[1][3:0]     = i_data[7:4];
        u_arr[0].hue      = RED;
        u_arr[0].payload  = CONST_VAL;
        o_data            = p_arr[0] ^ u_arr[0].payload;
    end
endmodule
//=========================================================
//=========================================================
module m_complex_arrays
(
    input  logic [15:0] i_val,
    output logic [15:0] o_val
);
    int dyn_arr[];
    int assoc_arr[int];
    int q_arr [$];
    string fmt_str;
    always_comb begin
        dyn_arr = new[4];
        dyn_arr[0] = i_val;
        q_arr.push_back(i_val);
        assoc_arr[i_val] = i_val;
        fmt_str = $sformatf("Val=%0d", i_val);
        o_val = dyn_arr[0] + q_arr[0] + assoc_arr[i_val];
    end
endmodule
//=========================================================
//=========================================================
module m_class_and_cast
(
    input  logic [31:0] i_num,
    output logic [31:0] o_num
);
    class simple_c;
        int v;
        function new(int x); v = x; endfunction
        function int get(); return v; endfunction
    endclass
    property non_zero(input int x);
        x != 0;
    endproperty
    always_comb begin
        int unsigned tmp = int'(i_num);
        simple_c c_inst = new(tmp);
        assert (non_zero(c_inst.get()));
        o_num = c_inst.get();
    end
endmodule
//=========================================================
//=========================================================
import "DPI-C" function int dpi_add (input int a, input int b);
module m_dpi_feature
(
    input  int a_in,
    input  int b_in,
    output int c_out
);
    (* keep = "true" *) logic dummy_attr;
    always_comb begin
        c_out      = dpi_add(a_in, b_in);
        dummy_attr = 1'b0;
    end
endmodule
//=========================================================
//=========================================================
module m_event_control
(
    input  logic clk,
    input  logic rst_n,
    output logic [7:0] cnt_out
);
    logic [7:0] counter;
    covergroup cg_counter @(posedge clk);
        coverpoint counter;
    endgroup
    cg_counter cg_inst = new;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter <= '0;
        else
            counter <= counter + 1;
    end
    assign cnt_out = counter;
endmodule
