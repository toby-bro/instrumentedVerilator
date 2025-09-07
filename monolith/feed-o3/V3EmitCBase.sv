module func_mod #(parameter WIDTH = 8) (
    input  logic                         clk,
    input  logic [WIDTH-1:0]             i_data,
    output logic [WIDTH-1:0]             o_data
);
    function automatic logic [WIDTH-1:0] inc(input logic [WIDTH-1:0] v);
        inc = v + 1;
    endfunction
    task automatic swap_incr(
        inout logic [WIDTH-1:0] a,
        inout logic [WIDTH-1:0] b
    );
        logic [WIDTH-1:0] tmp;
        tmp = a;
        a   = inc(b);
        b   = inc(tmp);
    endtask
    logic [WIDTH-1:0] a_reg, b_reg;
    always_ff @(posedge clk) begin
        a_reg <= i_data;
        b_reg <= o_data;
        swap_incr(a_reg, b_reg);
        o_data <= a_reg;
    end
endmodule
module dpi_mod (
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    output logic [31:0] o_sum
);
    import "DPI-C" function int c_add(input int a, input int b);
    export "DPI-C" function sv_mul;
    function int sv_mul(input int x, input int y);
        sv_mul = x * y;
    endfunction
    always_comb begin
        o_sum = c_add(i_a, i_b);
    end
endmodule
module class_mod (
    input  logic       clk,
    input  logic       rst,
    input  logic [7:0] i_val,
    output logic [7:0] o_val
);
    class base_c;
        virtual function int transform(input int v);
            transform = v;
        endfunction
    endclass
    class derived_c extends base_c;
        function int transform(input int v);
            transform = v << 1;
        endfunction
    endclass
    derived_c h;
    always_ff @(posedge clk) begin
        if (rst) begin
            h = new();
        end
        if (h != null) o_val <= h.transform(i_val);
        else           o_val <= '0;
    end
endmodule
module array_mod (
    input  logic        clk,
    input  logic [3:0]  i_idx,
    input  logic [7:0]  i_data,
    output logic [7:0]  o_data
);
    logic [7:0] mem [0:15];
    logic [3:0][7:0] packed_vec;
    always_ff @(posedge clk) begin
        mem[i_idx]             <= i_data;
        packed_vec[i_idx[1:0]] <= i_data;
        o_data                 <= mem[i_idx] ^ packed_vec[i_idx[1:0]];
    end
endmodule
module struct_mod (
    input  logic       clk,
    input  logic [7:0] i_in,
    output logic [7:0] o_out
);
    typedef struct packed {
        logic [3:0] low;
        logic [3:0] high;
    } nibble_s;
    nibble_s s;
    always_ff @(posedge clk) begin
        s.low  <= i_in[3:0];
        s.high <= i_in[7:4];
        o_out  <= {s.high, s.low};
    end
endmodule
module inout_mod (
    input  logic dir,
    input  logic value_in,
    inout  wire  data_pin,
    output wire  value_out
);
    assign data_pin  = dir ? value_in : 1'bz;
    assign value_out = data_pin;
endmodule
module string_mod (
    input  logic clk,
    input  logic start,
    output logic done
);
    string internal_str;
    always_ff @(posedge clk) begin
        if (start) begin
            internal_str = "hello_verilator";
            done <= 1'b1;
        end else begin
            done <= 1'b0;
        end
    end
endmodule
module multidim_mod (
    input  logic        clk,
    input  logic [1:0]  sel_row,
    input  logic [1:0]  sel_col,
    input  logic [15:0] i_val,
    output logic [15:0] o_val
);
    logic [15:0] matrix [0:3][0:3];
    function automatic void write_cell(
        input int row,
        input int col,
        input logic [15:0] val
    );
        matrix[row][col] = val;
    endfunction
    function automatic logic [15:0] read_cell(
        input int row,
        input int col
    );
        read_cell = matrix[row][col];
    endfunction
    always_ff @(posedge clk) begin
        write_cell(sel_row, sel_col, i_val);
        o_val <= read_cell(sel_row, sel_col);
    end
endmodule
module vm_sig_mod (
    input  logic clk,
    output logic __Vm_sig_status
);
    always_ff @(posedge clk) begin
        __Vm_sig_status <= ~__Vm_sig_status;
    end
endmodule
module wide_mod (
    input  logic         clk,
    input  logic [255:0] i_wide,
    output logic [255:0] o_wide
);
    always_ff @(posedge clk) begin
        o_wide <= i_wide;
    end
endmodule
