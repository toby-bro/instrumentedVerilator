module SimpleCombinationalLogic (
    input logic [7:0] in_data_a,
    input logic [1:0] in_sel,
    output logic [7:0] out_result_a
);
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_OP1  = 2'b01,
        STATE_OP2  = 2'b10,
        STATE_ERR  = 2'b11
    } sel_state_e;
    sel_state_e current_state;
    logic [7:0] temp_val;
    always_comb begin
        current_state = sel_state_e'(in_sel); 
        temp_val = 8'h00; 
        case (current_state)
            STATE_IDLE: temp_val = in_data_a;
            STATE_OP1:  temp_val = in_data_a + 8'd10;
            STATE_OP2:  temp_val = in_data_a - 8'd5;
            default:    temp_val = 8'hFF; 
        endcase
    end
    assign out_result_a = temp_val;
endmodule
module SequentialAndParameters (
    input logic         clk_i,
    input logic         rst_ni,
    input logic [15:0]  data_in_i,
    output logic [15:0] data_out_o
);
    parameter DATA_WIDTH = 16;
    parameter INIT_VALUE = 16'hAAAA;
    logic [DATA_WIDTH-1:0] register_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            register_q <= INIT_VALUE;
        end else begin
            register_q <= data_in_i;
        end
    end
    assign data_out_o = register_q;
endmodule
module ComplexDataTypes (
    input logic [3:0] in_value,
    input logic       select_sum,
    output logic [7:0] out_complex_result
);
    typedef struct packed {
        logic [3:0] part_a;
        logic [3:0] part_b;
    } my_packed_struct_t;
    typedef union packed {
        logic [7:0] full_word;
        my_packed_struct_t parts;
    } my_packed_union_t;
    typedef logic [1:0] array_2d_t [1:0][1:0];
    array_2d_t my_2d_array;
    function automatic logic [7:0] calculate_sum (input my_packed_struct_t data_in);
        return data_in.part_a + data_in.part_b;
    endfunction
    my_packed_union_t u_data;
    logic [7:0] temp_sum;
    always_comb begin
        u_data.parts.part_a = in_value;
        u_data.parts.part_b = in_value + 4'd1;
        if (select_sum) begin
            temp_sum = calculate_sum(u_data.parts);
        end else begin
            temp_sum = u_data.full_word;
        end
        my_2d_array[0][0] = 2'b00;
        my_2d_array[0][1] = 2'b01;
        my_2d_array[1][0] = 2'b10;
        my_2d_array[1][1] = 2'b11;
    end
    assign out_complex_result = temp_sum + my_2d_array[1][1];
endmodule
module ClassUsageExample (
    input logic in_trigger,
    output logic [7:0] out_class_value
);
    class MySimpleClass;
        rand int m_data; 
        function new();
            m_data = 10;
        endfunction
        function int get_data();
            return m_data;
        endfunction
    endclass
    MySimpleClass class_obj; 
    initial begin
        class_obj = new(); 
        void'(class_obj.randomize()); 
    end
    always_comb begin
        if (class_obj != null) begin 
            out_class_value = class_obj.get_data() + (in_trigger ? 8'd1 : 8'd0);
        end else begin
            out_class_value = 8'hAA; 
        end
    end
endmodule
module AssertionAndGenerate (
    input logic clk_i,
    input logic rst_ni,
    input logic [2:0] input_code,
    output logic [2:0] output_processed
);
    assert (input_code inside {[0:7]}) else $error("Input code out of range!");
    property p_valid_state;
        @(posedge clk_i) disable iff (!rst_ni) (input_code == 3'd4);
    endproperty
    ap_valid_state: assert property (p_valid_state) else $error("Input code was not 4!");
    genvar i;
    for (i = 0; i < 3; i++) begin : gen_loop_blocks
        logic [2:0] local_wire;
        assign local_wire = input_code + i;
        if (i == 1) begin : check_one
            assign output_processed[i] = local_wire[i];
        end else begin : default_assign
            assign output_processed[i] = local_wire[i];
        end
    end
endmodule
interface MemoryInterface (input logic clk);
    logic        write_en;
    logic        read_en;
    logic [7:0]  addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    modport Master (
        output write_en,
        output read_en,
        output addr,
        output wdata,
        input rdata,
        input clk
    );
    modport Slave (
        input write_en,
        input read_en,
        input addr,
        input wdata,
        output rdata,
        input clk
    );
endinterface
module InterfaceUser (
    input logic         clk_i,
    input logic         rst_ni,
    input logic         master_op_en,
    input logic [7:0]   master_addr,
    input logic [31:0]  master_wdata,
    output logic [31:0] slave_rdata_out
);
    MemoryInterface mem_if (.clk(clk_i));
    always_comb begin
        mem_if.write_en = master_op_en;
        mem_if.read_en  = !master_op_en;
        mem_if.addr     = master_addr;
        mem_if.wdata    = master_wdata;
    end
    logic [31:0] memory [255:0];
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
        end else begin
            if (mem_if.write_en) begin
                memory[mem_if.addr] <= mem_if.wdata;
            end
        end
    end
    assign mem_if.rdata = mem_if.read_en ? memory[mem_if.addr] : 32'hX;
    assign slave_rdata_out = mem_if.rdata;
endmodule
