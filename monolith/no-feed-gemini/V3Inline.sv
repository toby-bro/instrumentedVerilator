module mod_simple_logic (
    input logic [7:0] in_val,
    output logic [7:0] out_add,
    output logic [7:0] out_mult,
    output logic       out_reg
);
    logic [7:0] internal_reg;
    always_ff @(posedge in_val[0]) begin
        internal_reg <= in_val + 1;
        out_reg <= in_val[7];
    end
    assign out_add = in_val + 2;
    assign out_mult = in_val * 3;
endmodule
(* verilator_inline *)
module mod_inline_me (
    input logic in_a,
    input logic in_b,
    output logic out_c,
    output logic out_d
);
    assign out_c = in_a ^ in_b;
    assign out_d = in_a & in_b;
endmodule
(* verilator_noinline *)
module mod_no_inline_me (
    input logic in_x,
    output logic out_y
);
    assign out_y = ~in_x;
endmodule
module mod_complex_features (
    input logic [15:0] in_data_c,
    output logic [15:0] out_data_c,
    output logic        out_status_c
);
    class MyDataClass;
        rand int my_int_var;
        localparam int CLASS_CONST = 100;
        function new();
            my_int_var = 5;
        endfunction
        function int get_scaled_value(int scale_factor);
            return my_int_var * scale_factor + CLASS_CONST;
        endfunction
    endclass
    MyDataClass my_object; 
    typedef struct packed {
        logic [3:0] field1;
        logic       field2;
    } MyPackedStruct_t;
    MyPackedStruct_t local_struct;
    logic [7:0] unpacked_array [0:3];
    var public logic [7:0] public_signal;
    function automatic logic [15:0] calculate_checksum(logic [15:0] data_in);
        return data_in + data_in[7:0] + data_in[15:8];
    endfunction
    task automatic process_data(input logic [7:0] p_in, output logic p_out);
        p_out = p_in[0] | p_in[7];
        public_signal = p_in;
        unpacked_array[0] = p_in + 1;
        unpacked_array[1] = p_in + 2;
    endtask
    initial static begin
        my_object = new();
        local_struct.field1 = 4'b1010;
        local_struct.field2 = 1'b1;
    end
    logic [15:0] checksum_val;
    logic        task_out_bit;
    always_comb begin
        checksum_val = calculate_checksum(in_data_c);
        out_data_c = checksum_val + {local_struct.field1, local_struct.field2};
        out_status_c = public_signal[0];
    end
    always_ff @(posedge in_data_c[0]) begin
        process_data(in_data_c[7:0], task_out_bit);
    end
endmodule
interface MyInterface (input logic clk);
    logic [3:0] req;
    logic [3:0] resp;
    modport Master (output req, input resp, input clk);
    modport Slave (input req, output resp, input clk);
endinterface
module mod_interface_user (
    input logic           clk,
    MyInterface.Master    master_if,
    output logic [3:0]    output_val
);
    logic [3:0] internal_req;
    assign master_if.req = internal_req;
    assign output_val = master_if.resp;
    always_ff @(posedge clk) begin
        internal_req <= internal_req + 1;
    end
endmodule
module mod_hier_target (
    input logic in_data_t,
    output logic out_data_t
);
    logic internal_sig;
    assign internal_sig = in_data_t;
    assign out_data_t = internal_sig;
    function automatic logic get_internal_sig();
        return internal_sig;
    endfunction
    task automatic toggle_internal(output logic state);
        state = ~internal_sig;
    endtask
endmodule
module mod_hier_access (
    input logic in_access,
    output logic out_access
);
    mod_hier_target target_inst (.in_data_t(in_access), .out_data_t());
    logic func_result;
    logic task_state;
    assign func_result = target_inst.get_internal_sig();
    always_comb begin
        target_inst.toggle_internal(task_state);
        out_access = func_result ^ task_state;
    end
endmodule
(* verilator_inline *)
module mod_nested_inline (
    input logic in_nest,
    input logic in_nested_inline_a,
    input logic in_nested_inline_b,
    output logic out_nest_result,
    output logic out_nested_inline_c,
    output logic out_nested_inline_d,
    output logic out_nested_hier_val,
    output logic out_nested_hier_task_state
);
    mod_inline_me nested_inline_inst (
        .in_a (in_nested_inline_a),
        .in_b (in_nested_inline_b),
        .out_c(out_nested_inline_c),
        .out_d(out_nested_inline_d)
    );
    mod_hier_target non_inline_child_inst (
        .in_data_t(in_nest),
        .out_data_t(out_nest_result)
    );
    class InnerClass;
        int value = 0;
        function new(); value = 10; endfunction
    endclass
    InnerClass inner_obj;
    initial static begin
        inner_obj = new();
    end
    typedef enum {STATE_IDLE, STATE_BUSY} State_t;
    State_t current_state_inlined = STATE_IDLE; 
    function automatic int my_inlined_func(int arg);
        return arg * inner_obj.value;
    endfunction
    int func_res;
    always_comb begin
        func_res = my_inlined_func(1);
    end
    assign out_nested_hier_val = non_inline_child_inst.internal_sig;
    logic internal_task_state;
    always_comb begin
        non_inline_child_inst.toggle_internal(internal_task_state);
        out_nested_hier_task_state = internal_task_state;
    end
endmodule
module mod_coverage (
    input logic [3:0] data_in_cov,
    input logic       enable_cov,
    output logic      out_cov
);
    logic [1:0] state_cov;
    assign out_cov = enable_cov & data_in_cov[0];
    covergroup my_cg @(posedge enable_cov);
        option.per_instance = 1;
        coverpoint data_in_cov {
            bins zero = {0};
            bins all_on = {15};
            bins others = default;
        }
        data_state_cp: coverpoint state_cov {
            bins s0 = {0};
            bins s1 = {1};
            bins s2_s3 = {[2:3]};
        }
    endgroup
    my_cg cg_inst = new();
    always_ff @(posedge enable_cov) begin
        state_cov <= data_in_cov[1:0];
    end
endmodule
module design_top (
    input logic clk,
    input logic [7:0] in_main,
    output logic [7:0] out_main
);
    logic [7:0] logic_add, logic_mult;
    logic logic_reg;
    mod_simple_logic msl_inst (.in_val(in_main), .out_add(logic_add), .out_mult(logic_mult), .out_reg(logic_reg));
    logic inline_c, inline_d;
    mod_inline_me inline_inst_1 (.in_a(in_main[0]), .in_b(in_main[1]), .out_c(inline_c), .out_d(inline_d));
    mod_inline_me inline_inst_2 (.in_a(in_main[2]), .in_b(in_main[3]), .out_c(), .out_d());
    mod_inline_me inline_inst_3 (.in_a(in_main[4]), .in_b(in_main[5]), .out_c(), .out_d());
    logic no_inline_y;
    mod_no_inline_me no_inline_inst (.in_x(in_main[6]), .out_y(no_inline_y));
    logic [15:0] complex_out;
    logic complex_status;
    mod_complex_features mcf_inst (.in_data_c({in_main, logic_add}), .out_data_c(complex_out), .out_status_c(complex_status));
    MyInterface my_if(clk);
    mod_interface_user miu_inst (.clk(clk), .master_if(my_if.Master), .output_val());
    logic access_result;
    mod_hier_access mha_inst (.in_access(in_main[7]), .out_access(access_result));
    logic nested_out_result, nested_inline_c, nested_inline_d, nested_hier_val, nested_hier_task_state;
    mod_nested_inline mni_inst (
        .in_nest(in_main[0]),
        .in_nested_inline_a(in_main[1]),
        .in_nested_inline_b(in_main[2]),
        .out_nest_result(nested_out_result),
        .out_nested_inline_c(nested_inline_c),
        .out_nested_inline_d(nested_inline_d),
        .out_nested_hier_val(nested_hier_val),
        .out_nested_hier_task_state(nested_hier_task_state)
    );
    logic cov_out;
    mod_coverage mc_inst (.data_in_cov(in_main[3:0]), .enable_cov(in_main[0]), .out_cov(cov_out));
    assign out_main = logic_add[7:0] + complex_out[7:0] +
                      {inline_c, inline_d, no_inline_y, access_result, nested_out_result, nested_inline_c, cov_out, nested_hier_val ^ nested_hier_task_state};
endmodule
