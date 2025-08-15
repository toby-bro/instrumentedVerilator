package pkg_ex;
  int pkg_var = 5;
endpackage
interface simple_if;
  logic a;
endinterface
interface bus_if;
  logic a;
  modport slave (input a);
  modport master (output a);
endinterface
module array_examples (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    int dyn_arr[];
    int q_arr[$];
    int assoc_arr[int];
    typedef int fixed_t[8];
    fixed_t fixed_arr;
    logic [7:0] packed_arr [0:3];
    always_comb begin
        int sum;
        if (dyn_arr.size() == 0) begin
            dyn_arr = new[1];
            dyn_arr[0] = int'(in_data);
        end
        q_arr.push_back(int'(in_data));
        assoc_arr[int'(in_data)] = int'(in_data);
        sum = dyn_arr[0];
        if (q_arr.size() > 0) sum += q_arr[$-1];
        if (assoc_arr.exists(int'(in_data))) sum += assoc_arr[int'(in_data)];
        fixed_arr[0] = int'(in_data);
        sum += fixed_arr[0];
        packed_arr[0] = in_data[7:0];
        out_data = sum;
    end
endmodule
module struct_examples (
    input  logic clk,
    output logic [7:0] packed_out
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_s;
    packed_s ps;
    always_comb begin
        ps.a = clk ? 4'd1 : 4'd0;
        ps.b = clk ? 4'd2 : 4'd0;
        packed_out = ps.a + ps.b;
    end
endmodule
module enum_examples (
    input  logic [1:0] in_sig,
    output logic [1:0] out_sig
);
    typedef enum logic [1:0] {S0 = 2'd0, S1 = 2'd1, S2 = 2'd2} state_t;
    state_t state_var;
    always_comb begin
        state_var = state_t'(in_sig);
        out_sig   = logic'(state_var);
    end
endmodule
module param_type_mod #(
    parameter type T = int
) (
    input  logic [7:0] in_val,
    output      T      out_val
);
    T var_t;
    always_comb begin
        var_t   = T'(in_val);
        out_val = var_t;
    end
endmodule
module class_examples (
    input  logic din,
    output logic dout
);
    class my_class;
        int x;
        function void set(int v); x = v; endfunction
        function int get(); return x; endfunction
    endclass
    my_class handle;
    always_comb begin
        handle = null;
        if (din) handle = new();
        dout = (handle != null);
    end
endmodule
module interface_examples (
    input  logic sig_in,
    output logic sig_out
);
    always_comb sig_out = sig_in;
endmodule
module ref_dtype_examples (
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    typedef logic [7:0] byte_t;
    byte_t my_byte;
    always_comb begin
        my_byte  = in_byte;
        out_byte = my_byte;
    end
endmodule
import "DPI-C" function int dpi_add (input int a, input int b);
module dpi_examples (
    input  int a_in,
    output int b_out
);
    always_comb b_out = dpi_add(a_in, a_in);
endmodule
module sformat_examples (
    input  logic [15:0] val_in,
    output logic [15:0] val_out
);
    string str;
    always_comb begin
        str      = $sformatf("value=%0d", val_in);
        val_out  = val_in ^ str.len();
    end
endmodule
module modport_examples (
    bus_if.master m_if,
    bus_if.slave  s_if,
    input  logic sig_i,
    output logic sig_o
);
    always_comb begin
        m_if.a = sig_i;
        sig_o  = s_if.a;
    end
endmodule
module tasks_examples (
    input  logic clk,
    output logic task_bit
);
    task automatic do_something(ref int arr[]);
        int tmp;
        tmp = arr.size();
    endtask
    always_comb begin
        int local_arr[];
        local_arr = new[1];
        local_arr[0] = clk;
        do_something(local_arr);
        task_bit = (local_arr[0] != 0);
    end
endmodule
module cast_null_sel_examples (
    input  logic [7:0] data_in,
    output logic       null_flag
);
    class C; endclass
    C handle;
    logic [3:0] sub_sel;
    always_comb begin
        sub_sel = data_in[3:0];
        if (handle == null && data_in[0]) handle = new();
        null_flag = (handle == null);
    end
endmodule
