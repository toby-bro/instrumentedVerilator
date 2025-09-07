module SimpleTypesModule (
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic [7:0]  data_in_byte,
    input  int          value_in_int,
    output logic [7:0]  data_out_byte,
    output int          result_out_int
);
    logic [7:0]  internal_byte_reg;
    int          internal_int_reg;
    bit          status_flag;
    byte         counter_byte;
    class MySimpleClass;
        int class_id;
        function new(int id);
            this.class_id = id;
        endfunction
        function int get_id();
            return class_id;
        endfunction
    endclass
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            internal_byte_reg <= 8'h00;
            internal_int_reg  <= 0;
            status_flag       <= 1'b0;
            counter_byte      <= 8'h00;
        end else begin
            internal_byte_reg <= data_in_byte;
            internal_int_reg  <= value_in_int;
            status_flag       <= (data_in_byte > 8'h80);
            counter_byte      <= counter_byte + 1;
            begin : class_inst_block_1
                MySimpleClass simple_obj = new(10);
                if (simple_obj.get_id() == 10) begin
                    result_out_int <= simple_obj.class_id + value_in_int;
                end
            end
        end
    end
    always_comb begin
        data_out_byte = internal_byte_reg + counter_byte;
        if (status_flag) begin
            data_out_byte = data_out_byte + 1;
        end
        result_out_int = internal_int_reg * 2;
    end
endmodule
module ArrayAndStructModule (
    input  logic        clk_i,
    input  logic [3:0]  addr_in,
    input  logic [7:0]  data_val_in,
    output logic [7:0]  array_data_out,
    output logic [15:0] struct_status_out
);
    logic [7:0] unpacked_mem [16];
    logic [127:0] packed_data_bus;
    typedef struct packed {
        logic [7:0] id;
        logic [7:0] value;
    } Packet_t;
    Packet_t current_packet;
    typedef struct {
        logic [15:0] status_code;
        int          error_count;
    } SystemStatus_t;
    SystemStatus_t sys_status_reg;
    class MyComplexClass;
        Packet_t obj_packet;
        logic [7:0] obj_array [4];
        function new(Packet_t pkt_in);
            obj_packet = pkt_in;
            foreach(obj_array[i]) obj_array[i] = i;
        endfunction
        function logic [15:0] get_status();
            return {obj_packet.id, obj_packet.value};
        endfunction
    endclass
    always_ff @(posedge clk_i) begin
        unpacked_mem[addr_in] <= data_val_in;
        packed_data_bus       <= {packed_data_bus[126:0], data_val_in[0]}; 
        current_packet.id     <= addr_in;
        current_packet.value  <= data_val_in;
        sys_status_reg.status_code <= sys_status_reg.status_code + 1;
        sys_status_reg.error_count <= sys_status_reg.error_count + 1;
        begin : class_inst_block_2
            MyComplexClass complex_obj = new(current_packet);
            struct_status_out <= complex_obj.get_status();
        end
    end
    always_comb begin
        array_data_out    = unpacked_mem[addr_in];
        struct_status_out = sys_status_reg.status_code + (packed_data_bus[0] ? 1 : 0);
        if (sys_status_reg.error_count > 100) begin
            struct_status_out = struct_status_out | 16'hFFFF;
        end
    end
endmodule
module FunctionTaskStaticModule (
    input  logic        clk_i,
    input  logic        enable_i,
    input  int          input_val,
    output int          output_sum,
    output logic [15:0] status_code_out
);
    function automatic int calc_accum_sum(int add_val);
        static int accum = 0;
        accum = accum + add_val;
        return accum;
    endfunction
    task automatic update_status(input int val, output logic [15:0] status);
        int temp_local_var; 
        temp_local_var = val * 2;
        status = temp_local_var + 100;
        class TaskHelperClass;
            string message = "Task Executed";
            function string get_msg(); return message; endfunction
        endclass
        TaskHelperClass helper_obj = new();
        if (helper_obj.get_msg() != "") begin
            status = status + 1;
        end
    endtask
    int module_internal_sum;
    logic [15:0] module_status;
    always_ff @(posedge clk_i) begin
        if (enable_i) begin
            module_internal_sum <= calc_accum_sum(input_val);
            update_status(module_internal_sum, module_status);
        end
    end
    always_comb begin
        output_sum      = module_internal_sum;
        status_code_out = module_status;
    end
endmodule
module EnumAndUnionModule (
    input  logic        clk_i,
    input  logic [1:0]  op_select,
    input  byte         operand_a,
    input  byte         operand_b,
    output int          calc_result_out,
    output logic [7:0]  union_val_out
);
    typedef enum logic [1:0] {
        ADD = 2'b00,
        SUB = 2'b01,
        MUL = 2'b10,
        DIV = 2'b11
    } Operation_e;
    Operation_e current_op;
    typedef union packed {
        byte byte_val;
        logic [7:0] bit_vec_val;
    } DataUnion_t;
    DataUnion_t my_data_union;
    int internal_result;
    byte internal_byte_val;
    class MyUnionClass;
        DataUnion_t u_val;
        function new(DataUnion_t init_val);
            u_val = init_val;
        endfunction
        function byte get_byte(); return u_val.byte_val; endfunction
    endclass
    always_ff @(posedge clk_i) begin
        current_op <= Operation_e'(op_select);
        my_data_union.byte_val <= operand_a; 
        internal_byte_val <= my_data_union.byte_val; 
    end
    always_comb begin
        case (current_op)
            ADD: internal_result = operand_a + operand_b;
            SUB: internal_result = operand_a - operand_b;
            MUL: internal_result = operand_a * operand_b;
            DIV: begin
                if (operand_b != 0) internal_result = operand_a / operand_b;
                else internal_result = 0;
            end
            default: internal_result = 0;
        endcase
        calc_result_out = internal_result;
        begin : class_inst_block_3
            MyUnionClass union_obj = new(my_data_union);
            union_val_out = union_obj.get_byte();
            if (my_data_union.bit_vec_val == 8'hFF) begin
                union_val_out = 8'h00;
            end
        end
    end
endmodule
module WideDataModule (
    input  logic        clk_i,
    input  logic [127:0] data_in_128,
    input  logic [255:0] data_in_256,
    output logic [127:0] data_out_128,
    output real          real_sum_out
);
    logic [1023:0] very_wide_register;
    longint        large_integer_val;
    real           float_value_1;
    real           float_value_2;
    class MyRealClass;
        real r_val;
        function new(real init_val);
            r_val = init_val;
        endfunction
        function real get_r_val(); return r_val; endfunction
    endclass
    always_ff @(posedge clk_i) begin
        very_wide_register <= {very_wide_register[255:0], data_in_256, data_in_128}; 
        large_integer_val  <= large_integer_val + 1;
        float_value_1      <= 1.0;
        float_value_2      <= 2.5;
        begin : class_inst_block_4
            MyRealClass real_obj = new(float_value_1 + float_value_2);
            real_sum_out <= real_obj.get_r_val();
        end
    end
    always_comb begin
        data_out_128 = very_wide_register[127:0];
        real_sum_out = float_value_1 + float_value_2 + large_integer_val;
        if (very_wide_register[1000] == 1) begin
            data_out_128 = 128'hFFFF_FFFF_FFFF_FFFF;
        end
    end
endmodule
module ParameterModule #(
    parameter DATA_WIDTH = 16,
    parameter DEPTH = 8
) (
    input  logic clk_i,
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out
);
    localparam LOCAL_FACTOR = 4;
    localparam MAX_VAL = (1 << DATA_WIDTH) - 1;
    logic [DATA_WIDTH-1:0] internal_reg_array [DEPTH]; 
    logic [DATA_WIDTH-1:0] processed_data;
    class ParamClass;
        int p_width;
        function new(int width);
            p_width = width;
        endfunction
        function int get_p_width(); return p_width; endfunction
    endclass
    always_ff @(posedge clk_i) begin
        for (int i = 0; i < DEPTH; i++) begin
            if (i == 0) internal_reg_array[i] <= data_in;
            else internal_reg_array[i] <= internal_reg_array[i-1] * LOCAL_FACTOR;
        end
        begin : class_inst_block_5
            ParamClass p_obj = new(DATA_WIDTH);
            if (p_obj.get_p_width() > 0) begin
                processed_data <= p_obj.get_p_width() + data_in;
            end
        end
    end
    always_comb begin
        data_out = processed_data;
        if (internal_reg_array[DEPTH-1] > MAX_VAL / 2) begin
            data_out = MAX_VAL;
        end
    end
endmodule
module PortVarietyModule (
    input  bit [0:0]          bit_in,     
    input  shortint           shortint_in,
    input  longint unsigned   longint_u_in,
    output byte               byte_out,
    output integer            integer_out,
    output longint            longint_s_out
);
    chandle opaque_handle;
    event trigger_event;
    byte internal_byte_val;
    integer internal_integer_val;
    longint internal_longint_val;
    class OpaqueClass;
        chandle h_val;
        function new(chandle init_h); h_val = init_h; endfunction
        function chandle get_h_val(); return h_val; endfunction
    endclass
    always_comb begin
        internal_byte_val    = byte'(shortint_in + bit_in);
        internal_integer_val = integer'(longint_u_in);
        internal_longint_val = longint_u_in;
        byte_out      = internal_byte_val;
        integer_out   = internal_integer_val;
        longint_s_out = internal_longint_val;
        begin : class_inst_block_6
            opaque_handle = null; 
            OpaqueClass opaque_obj = new(opaque_handle);
            if (opaque_obj.get_h_val() == null) begin
                byte_out = byte_out + 1;
            end
        end
        -> trigger_event; 
    end
endmodule
