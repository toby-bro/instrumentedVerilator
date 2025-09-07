package my_pkg_types;
    typedef logic [15:0] word_t;
    typedef enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} fsm_state_e;
    typedef struct packed {
        logic [3:0] id;
        logic valid;
    } header_s;
    class MyFwdClass;
        int dummy_val;
    endclass
    class ParameterizedClass #(parameter int SIZE = 8);
        logic [SIZE-1:0] data;
        function new; data = '0; endfunction
    endclass
    MyFwdClass my_fwd_inst; 
endpackage
interface axi_if (input logic aclk);
    logic [31:0] awaddr;
    logic [31:0] wdata;
    logic awvalid;
    logic awready;
    modport master (
        output awaddr,
        output wdata,
        output awvalid,
        input awready
    );
    task write_data (input logic [31:0] addr, input logic [31:0] data);
        awaddr = addr;
        wdata = data;
        awvalid = 1'b1;
        @(posedge aclk) begin
            while (!awready) @(posedge aclk);
        end
        awvalid = 1'b0;
    endtask : write_data
endinterface
module CoreDeclarations (
    input logic [7:0] in_val,
    input int in_count,
    output logic [15:0] out_data,
    output int out_status
);
    logic [7:0] my_byte = 8'hAA;
    int my_int_var;
    const logic MY_CONST_BIT = 1'b1; 
    function void set_int_var(int val);
        my_int_var = val; 
    endfunction
    always_comb begin
        my_byte = in_val[7:0];
        out_data = 16'(in_count) + my_byte;
        set_int_var(in_count + MY_CONST_BIT); 
        out_status = my_int_var;
    end
endmodule
module StructuredAndArrayTypes (
    input logic [7:0] input_byte,
    input int index_in,
    output logic [7:0] output_byte
);
    import my_pkg_types::*;
    word_t data_word; 
    header_s header_info; 
    logic [7:0] fixed_size_array [4];
    logic [7:0] dynamic_array [];
    logic [7:0] assoc_array_str [string];
    logic [7:0] assoc_array_wildcard_key [*]; 
    logic [7:0] assoc_array_default [int] = '{default: 8'hFF}; 
    logic [7:0] fifo_queue [$];
    function automatic logic [7:0] process_unsized_array(input logic [7:0] data_arr []); 
        return data_arr[0] + 1;
    endfunction
    ParameterizedClass #(16) my_param_object; 
    always_comb begin
        data_word = {input_byte, input_byte};
        header_info.id = input_byte[3:0]; 
        header_info.valid = input_byte[0];
        fixed_size_array[0] = input_byte;
        fixed_size_array[1] = process_unsized_array('{input_byte, input_byte + 1});
        dynamic_array = new[2]; 
        dynamic_array[0] = input_byte;
        dynamic_array[1] = input_byte + 1;
        assoc_array_str["first"] = input_byte; 
        assoc_array_wildcard_key[index_in] = input_byte; 
        fifo_queue.push_back(input_byte); 
        my_param_object = new(); 
        my_param_object.data = data_word; 
        output_byte = fixed_size_array[1] ^ dynamic_array[0] ^ assoc_array_str["first"] ^ assoc_array_wildcard_key[index_in] ^ fifo_queue.pop_front() ^ assoc_array_default[10];
    end
endmodule
module ControlFlowAndSystemTasks (
    input logic clk,
    input logic reset_n,
    input logic [3:0] input_val,
    output logic [3:0] output_cnt
);
    logic [3:0] counter;
    class DataPacket;
        int id;
        function new(int p_id); id = p_id; endfunction
    endclass
    DataPacket my_packet;
    logic [3:0] foreach_arr [4] = '{1,2,3,4};
    int total_sum_loop;
    always_ff @(posedge clk or negedge reset_n) begin 
        begin
            if (!reset_n) begin
                counter <= 4'b0;
                if (my_packet != null) begin
                    my_packet.id = 0;
                end else begin
                    my_packet = new(0);
                end
            end else begin
                for (int i=0; i<4; i++) begin : for_loop_block 
                    if (input_val[i]) begin
                        counter <= counter + 1;
                        if (counter > 10) begin
                            break; 
                        end
                    end else if (i == 2) begin
                        continue; 
                    end
                end : for_loop_block
                $info("Counter: %0d, Input: %0h", counter, input_val);
                if (input_val == 4'hF) begin
                    $error("Input is max!");
                end
                if (input_val[0]) begin
                    $monitoroff;
                end
            end
        end
    end
    localparam string MSG = $sformatf("Value is %0d", 5);
    property check_input;
        @(posedge clk) (input_val > 0);
    endproperty
    assert property (check_input); 
    cover property (check_input); 
    covergroup my_val_cg @(posedge clk);
        option.per_instance = 1;
        coverpoint input_val; 
    endgroup
    my_val_cg cg_inst = new();
    function int parse_num(string s);
        int val;
        void'($sscanf(s, "Num: %0d", val)); 
        return val; 
    endfunction
    always_comb begin
        total_sum_loop = 0;
        foreach (foreach_arr[i]) begin 
            total_sum_loop += foreach_arr[i];
        end
        output_cnt = counter + parse_num("Num: 10") + total_sum_loop;
    end
endmodule
module HierarchyAndDPI (
    input logic clk,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    import my_pkg_types::*; 
    import my_library::*; 
    SubModule u_sub_inst ( 
        .sub_clk(clk),
        .sub_data_in(data_in),
        .sub_data_out(data_out)
    );
    axi_if bus_if (.aclk(clk)); 
    import "DPI-C" function int calculate_sum_dpi(int a, int b);
    DerivedClass my_obj; 
    always_comb begin : main_logic 
        logic [7:0] temp_val; 
        int dpi_result;
        if (my_obj == null) begin
            my_obj = new(data_in[3:0]);
        end
        temp_val = data_in + my_obj.derived_val;
        bus_if.master.write_data(32'h1000, 32'hABCD);
        dpi_result = calculate_sum_dpi(data_in, temp_val); 
    end
endmodule
module SubModule (
    input logic sub_clk,
    input logic [7:0] sub_data_in,
    output logic [7:0] sub_data_out
);
    assign sub_data_out = sub_data_in + 1;
endmodule
