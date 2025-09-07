class GlobalDummySVClass;
    int m_data;
    function new();
        m_data = 0;
    endfunction
endclass
class GlobalMySVClass;
    int member_var;
    function new();
        member_var = 0;
    endfunction
    function void set_member(int val);
        this.member_var = val;
    endfunction
    function int get_member();
        return this.member_var;
    endfunction
endclass
module ModuleBasicTypes (
    input logic [7:0] in_a,
    input int in_b,
    output logic [15:0] out_c,
    output int out_d
);
    parameter int PARAM_INT = 10;
    localparam logic [31:0] LOCAL_PARAM_WIDE = 32'hFEED_BEEF;
    parameter string PARAM_STRING = "HelloVerilator";
    parameter real PARAM_REAL = 3.14;
    static logic [7:0] s_static_reg;
    logic [15:0] internal_reg_comb;
    int internal_var_ff;
    real internal_real_var;
    always_comb begin
        internal_reg_comb = in_a + PARAM_INT + s_static_reg;
        out_c = internal_reg_comb + LOCAL_PARAM_WIDE[15:0];
        internal_real_var = PARAM_REAL * 2.0;
    end
    always_ff @(posedge in_a[0]) begin
        internal_var_ff <= in_b * 2;
        s_static_reg <= in_a;
        out_d <= internal_var_ff;
    end
endmodule
module ModuleComplexDTypes (
    input bit [3:0] in_select,
    input int in_data_int,
    input logic [63:0] in_data_wide,
    output int out_calc_int,
    output logic [63:0] out_calc_wide
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_RUN  = 2'b01,
        STATE_STOP = 2'b10
    } my_state_e;
    typedef struct packed {
        logic [7:0] field_a;
        bit [15:0] field_b;
        my_state_e field_state;
    } my_packed_struct_t;
    typedef struct {
        int         field_u_int;
        string      field_u_string;
        my_state_e  field_u_state;
    } my_unpacked_struct_t;
    typedef union packed {
        logic [31:0] u_dword;
        my_packed_struct_t u_struct;
    } my_packed_union_t;
    my_packed_struct_t   s_internal_packed_struct;
    my_unpacked_struct_t s_internal_unpacked_struct;
    my_packed_union_t    u_internal_packed_union;
    my_state_e current_state;
    logic [31:0] temp_val;
    always_comb begin
        s_internal_packed_struct.field_a = in_select + 8'h10;
        s_internal_packed_struct.field_b = in_data_int + 16'h100;
        s_internal_packed_struct.field_state = (in_select == 0) ? STATE_IDLE : STATE_RUN;
        u_internal_packed_union.u_dword = in_data_int + in_data_wide[31:0];
        temp_val = u_internal_packed_union.u_struct.field_a + u_internal_packed_union.u_struct.field_b;
        out_calc_int = s_internal_packed_struct.field_b + in_data_int;
        out_calc_wide = {u_internal_packed_union.u_dword, temp_val} + in_data_wide;
        current_state = s_internal_packed_struct.field_state;
        s_internal_unpacked_struct.field_u_int = in_data_int * 2;
        s_internal_unpacked_struct.field_u_string = "Unpacked_Data";
        s_internal_unpacked_struct.field_u_state = STATE_STOP;
        out_calc_int = out_calc_int + s_internal_unpacked_struct.field_u_int;
    end
endmodule
module ModuleArraysAndClasses (
    input int in_idx,
    input logic [7:0] in_val,
    input real in_real_val,
    output logic [7:0] out_array_elem,
    output real out_real_calc
);
    logic [7:0] unpacked_array [0:7];
    logic [15:0] packed_array;
    logic [127:0] very_wide_packed_array;
    int queue_var [$];
    real double_var;
    logic [15:0] bus_var;
    logic bit_var;
    logic [65:0] quad_like_var;
    event my_event;
    GlobalDummySVClass sv_obj;
    GlobalDummySVClass sv_obj_array [];
    initial begin : sv_obj_instantiation
        sv_obj = new();
        sv_obj_array = new[2];
        foreach (sv_obj_array[i]) begin
            sv_obj_array[i] = new();
        end
    end
    always_comb begin
        unpacked_array[in_idx % 8] = in_val;
        out_array_elem = unpacked_array[7 - (in_idx % 8)];
        packed_array = {in_val, in_val};
        very_wide_packed_array = {128{in_val[0]}};
        if (in_idx == 0) begin
            queue_var.push_back(in_val);
        end else if (queue_var.size() > 0) begin
            queue_var.pop_front();
        end
        double_var = in_real_val * 1.5;
        out_real_calc = double_var;
        bus_var = {in_val, in_val[7:0]};
        bit_var = in_val[0];
        quad_like_var = {128'h1 + in_idx, 128'h2 + in_val};
    end
    always_ff @(posedge bit_var) begin
        -> my_event;
    end
    covergroup cg_array @(posedge in_val[0]);
        coverpoint in_idx {
            bins idx0 = {0};
            bins idx_range = {[1:7]};
        }
    endgroup
    cg_array instance_cg_array = new();
    always_comb begin
        if (sv_obj != null) begin
            sv_obj.m_data = in_idx;
        end
        if (sv_obj_array.size() > 0 && sv_obj_array[0] != null) begin
            sv_obj_array[0].m_data = in_val;
        end
    end
endmodule
module ModuleSystemCish (
    input logic clk,
    inout logic [7:0] s_inout_data,
    output logic [15:0] s_out_result
);
    logic [7:0] s_bv_internal;
    logic [15:0] s_uint_internal;
    logic [63:0] s_biguint_internal;
    always_ff @(posedge clk) begin
        s_bv_internal <= s_inout_data + 8'h1;
        s_uint_internal <= s_bv_internal + 16'h10;
        s_biguint_internal <= s_uint_internal + 64'h100;
        s_out_result <= s_uint_internal + s_biguint_internal[15:0];
        s_inout_data <= s_inout_data + 1;
    end
endmodule
module ModuleDPI (
    input int in_val_a,
    input int in_val_b,
    inout int inout_val_c,
    output int out_sum,
    output int out_product
);
    import "DPI-C" function int c_add(int a, int b);
    export "DPI-C" function int sv_multiply(int a, int b);
    function automatic int sv_multiply(int a, int b);
        return a * b + inout_val_c;
    endfunction
    always_comb begin
        out_sum = c_add(in_val_a, in_val_b);
        out_product = sv_multiply(in_val_a, in_val_b);
        inout_val_c = inout_val_c + in_val_a;
    end
endmodule
module ModuleSVClassMethod (
    input int in_val_m,
    output int out_res_m
);
    GlobalMySVClass obj_inst;
    initial begin
        obj_inst = new();
    end
    always_comb begin
        if (obj_inst != null) begin
            obj_inst.set_member(in_val_m + 5);
            out_res_m = obj_inst.get_member() + obj_inst.member_var;
        end else begin
            out_res_m = 0;
        end
    end
endmodule
