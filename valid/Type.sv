module integral_features #(parameter W = 32) (
    input  logic signed [W-1:0] in_signed,
    input  logic        [W-1:0] in_unsigned,
    output logic        [W-1:0] out_mix
);
    byte                 byte_var;
    shortint             s_short_signed;
    int unsigned         int_unsigned;
    longint              long_signed;
    time                 t_time;
    bit                  bit_scalar;
    logic                logic_scalar;
    reg                  reg_scalar;
    always_comb begin
        byte_var        = 8'(in_unsigned[7:0]);
        s_short_signed  = shortint'(in_signed[15:0]);
        int_unsigned    = int'(in_unsigned);
        long_signed     = longint'(in_signed);
        t_time          = time'(in_unsigned);
        bit_scalar      = in_unsigned[0];
        logic_scalar    = in_signed[0];
        reg_scalar      = in_signed[1];
        out_mix         = {byte_var, s_short_signed[7:0], int_unsigned[7:0], long_signed[7:0]};
    end
endmodule
module array_features(
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  addr,
    output logic [7:0]  data_out
);
    logic [7:0] mem_unpacked [0:15];
    logic [3:0][1:0] packed_vec;
    int dyn_arr[];
    int assoc_arr[int];
    int queue_var[$];
    always_ff @(posedge clk) begin
        if (rst) begin
            dyn_arr   = new[16];
            queue_var = {};
        end
        mem_unpacked[addr] <= addr;
        queue_var.push_back(addr);
    end
    always_comb begin
        assoc_arr[addr] = addr * 2;
        packed_vec      = addr;
        data_out        = mem_unpacked[addr];
    end
endmodule
module struct_union_features(
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    typedef struct packed {
        logic [3:0] nibble_high;
        logic [3:0] nibble_low;
    } packed_struct_t;
    typedef struct {
        int  word;
        byte byte_field;
    } unpacked_struct_t;
    typedef union packed {
        logic [7:0]      whole;
        logic [1:0][3:0] nibbles;
    } packed_union_t;
    packed_struct_t   p_struct;
    unpacked_struct_t u_struct;
    packed_union_t    p_union;
    always_comb begin
        p_struct.nibble_high = in_byte[7:4];
        p_struct.nibble_low  = in_byte[3:0];
        u_struct.word        = {24'd0, in_byte};
        u_struct.byte_field  = in_byte;
        p_union.whole        = in_byte;
        out_byte             = p_union.whole ^ {p_struct.nibble_high, p_struct.nibble_low};
    end
endmodule
module enum_features(
    input  logic       clk,
    input  logic [1:0] in_state,
    output logic       out_flag
);
    typedef enum bit [1:0] {
        S_IDLE = 2'd0,
        S_RUN  = 2'd1,
        S_WAIT = 2'd2,
        S_ERR  = 2'd3
    } state_e;
    state_e current;
    always_ff @(posedge clk) begin
        current <= state_e'(in_state);
    end
    assign out_flag = (current == S_RUN);
endmodule
import "DPI-C" function void dpi_add (input int a[], output int result);
module dpi_features(
    input  logic       clk,
    input  logic       rst,
    output logic [31:0] sum_out
);
    int values_dynamic[];
    int dpi_result;
    always_comb begin
        values_dynamic = new[4];
        values_dynamic = '{1,2,3,4};
        dpi_add(values_dynamic, dpi_result);
        sum_out = dpi_result;
    end
endmodule
module misc_features(
    input  logic       clk,
    input  logic       rst,
    output logic [7:0] out_cnt
);
    chandle     c_h;
    event       ev;
    string      str;
    int         counter;
    always_ff @(posedge clk) begin
        if (rst) begin
            counter <= 0;
            str     <= "rst";
        end
        else begin
            counter <= counter + 1;
            str     <= "running";
        end
    end
    assign out_cnt = counter[7:0];
endmodule
