module VarRefAssignStrengthMod (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    reg [7:0] internal_reg;
    wire [7:0] continuous_wire;
    parameter int PARAM_VAL = 10;
    assign (supply1, supply0) continuous_wire = in_data + 1;
    always_comb begin
        internal_reg = in_data;
    end
    assign out_result = continuous_wire;
endmodule
module ForceReleaseMod (
    input logic in_reset,
    output reg out_state
);
    reg data_reg;
    reg data_force;
    always_comb begin
        if (in_reset) begin
            force data_reg = 1'b0;
            release data_force;
        end else begin
            data_reg = data_force;
            data_force = 1'b1;
        end
    end
    assign out_state = data_reg;
endmodule
module InitialAndFuncMod (
    input int in_val,
    output int out_calc
);
    int static_var_a;
    int static_var_b;
    function automatic int calc_func(input int f_in, input int f_io_val);
        automatic int auto_local_var;
        auto_local_var = f_in + f_io_val;
        return auto_local_var;
    endfunction
    initial begin
        automatic int temp_auto_init;
        static_var_a = calc_func(10, in_val);
        temp_auto_init = calc_func(5, static_var_a);
        static_var_b = temp_auto_init;
    end
    assign out_calc = static_var_a + static_var_b;
endmodule
module FileIOSysTasksMod (
    input logic [31:0] in_data,
    output int out_status
);
    integer file_handle;
    string read_string;
    logic [7:0] mem_array [0:15];
    int scanned_val;
    string sscanf_str = "value 123";
    string sformatf_out;
    integer ferror_status;
    always_comb begin
        out_status = 0;
        file_handle = 32'h80000001;
        $ferror(file_handle, ferror_status);
        $fgets(read_string, file_handle);
        $fread(mem_array, file_handle);
        $fscanf(file_handle, "%d", scanned_val);
        $ungetc(in_data[7:0], file_handle); 
        $sscanf(sscanf_str, "value %d", scanned_val);
        $sformatf(sformatf_out, "Data is %0d", in_data);
        if (scanned_val == 0) out_status = 1;
        out_status = out_status + sformatf_out.len() + ferror_status;
    end
endmodule
module RandomAndDistMod (
    input bit in_enable_rand,
    output int out_rand_val
);
    class MyRandomizer;
        rand int r_data;
        rand bit r_valid;
        constraint c_data {
            r_data dist {10 := 40, 20 := 60};
            r_valid == 1'b1;
            r_data inside {[0:100], 200};
        }
        function new();
            r_data = 0;
            r_valid = 0;
        endfunction
    endclass
    MyRandomizer my_random_inst;
    initial begin
        my_random_inst = new();
        my_random_inst.r_data = $random(123);
    end
    always_comb begin
        if (in_enable_rand) begin
            if (!my_random_inst.randomize()) begin
            end
        end
        out_rand_val = my_random_inst.r_data;
    end
endmodule
module MemoryReadMod (
    input logic [7:0] in_address, 
    output logic [7:0] out_mem_data
);
    reg [7:0] memory [0:255];
    string filename_val = "memory_init.mem";
    initial begin
        $readmemb(filename_val, memory);
        memory[0] = 8'hAA; 
        memory[1] = 8'hBB;
    end
    always_comb begin
        out_mem_data = memory[in_address];
    end
endmodule
module PlusArgsAndSFormatfMod (
    input int in_value,
    output string out_formatted_string
);
    int plusarg_out_val;
    string plusarg_search_str = "+my_arg=";
    string fmt_str;
    always_comb begin
        if ($test$plusargs("+some_feature")) begin
        end
        $value$plusargs(plusarg_search_str, plusarg_out_val);
        $sformatf(fmt_str, "Input value is %0d", in_value);
        out_formatted_string = fmt_str;
        if (plusarg_out_val == 0) begin
            out_formatted_string = "Default";
        end
    end
endmodule
module UnaryOperatorsAndCastMod (
    input int in_operand,
    output int out_result
);
    int a, b, c, d;
    int cast_source_int;
    int cast_target_int;
    class MyBase;
        int val_base;
        function new(); val_base = 0; endfunction
    endclass
    class MyDerived extends MyBase;
        int val_derived;
        function new(); super.new(); val_derived = 0; endfunction
    endclass
    MyBase my_base_obj;
    MyDerived my_derived_obj;
    initial begin
        my_derived_obj = new();
    end
    always_comb begin
        a = in_operand;
        b = in_operand;
        c = in_operand;
        d = in_operand;
        ++a;
        b++;
        --c;
        d--;
        cast_source_int = in_operand * 3;
        $cast(cast_target_int, cast_source_int);
        if (my_derived_obj != null) begin
            $cast(my_base_obj, my_derived_obj);
        end else begin
            my_base_obj = null;
        end
        out_result = a + b + c + d + cast_target_int + (my_base_obj == null ? 0 : my_base_obj.val_base);
    end
endmodule
module SelectAndArrayRefMod (
    input logic [31:0] in_bus,
    output logic [31:0] out_modified_bus
);
    logic [31:0] reg_array [0:3];
    logic [7:0] sub_reg;
    int index_var = 1;
    always_comb begin
        out_modified_bus = in_bus;
        out_modified_bus[7:0] = in_bus[15:8];
        out_modified_bus[8] = in_bus[9];
        reg_array[index_var] = in_bus;
        reg_array[++index_var][15:0] = in_bus[15:0];
        reg_array[index_var--][7:0] = in_bus[7:0];
        reg_array[2][++index_var] = 1'b1;
        reg_array[3][index_var++] = 1'b0;
        sub_reg = reg_array[0][7:0];
    end
endmodule
module ClassMemberAndFuncCallMod (
    input int in_class_val,
    output int out_class_result
);
    class MyData;
        rand int member_data;
        int other_data;
        function void set_data(input int val);
            this.member_data = val;
        endfunction
        function int get_data();
            return this.member_data;
        endfunction
    endclass
    MyData my_instance;
    task automatic my_task(input int task_in, output int task_out);
        task_out = task_in * 2;
    endtask
    initial begin
        my_instance = new();
    end
    always_comb begin
        int task_intermediate;
        if (my_instance != null) begin
            my_instance.member_data = in_class_val + 5;
            my_instance.other_data = in_class_val;
            my_instance.set_data(in_class_val);
            my_instance.other_data = my_instance.get_data();
        end
        my_task(in_class_val, task_intermediate);
        out_class_result = (my_instance == null ? 0 : my_instance.member_data + my_instance.other_data) + task_intermediate;
    end
endmodule
module EventTriggerMod (
    input bit in_trigger,
    output bit out_fired
);
    event my_event;
    logic fired_flag;
    initial begin
    end
    always_comb begin
        if (in_trigger) begin
            -> my_event;
            fired_flag = 1'b1;
        end else begin
            fired_flag = 1'b0;
        end
        out_fired = fired_flag;
    end
endmodule
module SysIgnoreMod (
    input int in_val,
    output int out_len
);
    int dummy_var;
    typedef enum {RED, GREEN, BLUE} Color_e;
    Color_e my_color = RED;
    string type_name;
    always_comb begin
        dummy_var = in_val;
        out_len = $bits(in_val);
        type_name = $typename(my_color);
        if (dummy_var == 0) out_len = 0;
        else out_len = out_len + type_name.len();
    end
endmodule
module SubModule (
    output logic sub_output
);
    assign sub_output = 1'b1;
endmodule
module PinLValueMod (
    input logic in_dummy,
    output logic out_pin_value
);
    logic internal_signal;
    SubModule sub_inst (
        .sub_output(internal_signal) 
    );
    assign out_pin_value = internal_signal & in_dummy;
endmodule
