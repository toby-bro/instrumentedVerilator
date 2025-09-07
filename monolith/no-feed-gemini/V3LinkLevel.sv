timeunit 1ns/1ps;
timeprecision 1ps;
module module_top_multi (
    input  logic         clk,
    input  logic [7:0]   in_data,
    output logic [15:0]  out_sum,
    input  int           control_a,
    output int           status_b
);
    logic [7:0] middle_data;
    logic       flag_sig;
    int         result_int;
    module_ref_ports i_ref_ports (
        .clk_i      (clk),
        .data_in_i  (in_data),
        .modify_o   (middle_data), 
        .const_in_i (control_a),   
        .result_o   (result_int)    
    );
    always_comb begin
        out_sum = {middle_data, in_data};
        status_b = result_int + control_a;
        flag_sig = (middle_data > 8'h80);
    end
    class MySimpleClass;
        logic [3:0] value;
        function new();
            value = 4'h0;
        endfunction
        function void increment(input logic [3:0] amount);
            value = value + amount;
        endfunction
    endclass
    MySimpleClass my_instance;
    initial begin 
        my_instance = new();
    end
    always_comb begin
        if (clk) begin 
            my_instance.increment(middle_data[3:0]);
        end
    end
endmodule
interface interface_my_bus (input logic clk);
    logic [31:0] addr;
    logic [7:0]  data;
    logic        ready;
    logic        valid;
    modport master (
        output addr, data, valid,
        input ready
    );
    modport slave (
        input addr, data, valid,
        output ready
    );
endinterface
module module_with_interface_ports (
    input  logic             sys_clk,
    input  logic             reset_n,
    interface_my_bus.master i_bus_master,
    interface_my_bus.slave  o_bus_slave,
    interface_my_bus [1:0]  bus_array_ports 
);
    logic [31:0] internal_addr;
    logic [7:0]  internal_data;
    logic        internal_ready;
    logic        internal_valid;
    always_ff @(posedge sys_clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_addr <= 32'h0;
            internal_data <= 8'h0;
            internal_ready <= 1'b0;
            internal_valid <= 1'b0;
        end else begin
            i_bus_master.addr  = internal_addr + 1;
            i_bus_master.data  = internal_data;
            i_bus_master.valid = internal_valid;
            o_bus_slave.ready = 1'b1; 
            if (bus_array_ports[0].valid) begin
                bus_array_ports[0].ready = 1'b1;
            end
            if (bus_array_ports[1].valid) begin
                bus_array_ports[1].ready = 1'b1;
            end
            internal_addr <= internal_addr + 1;
            internal_data <= i_bus_master.data;
            internal_ready <= i_bus_master.ready;
            internal_valid <= 1'b1;
        end
    end
endmodule
module module_ref_ports (
    input        logic     clk_i,
    input        logic [7:0] data_in_i,
    output ref   logic [7:0] modify_o,
    input  const ref bit [3:0] const_in_i,
    output ref   int         result_o
);
    always_comb begin
        if (const_in_i[0]) begin
            modify_o = data_in_i + const_in_i[3:0];
        end else begin
            modify_o = data_in_i - const_in_i[3:0];
        end
        result_o = $signed(modify_o);
    end
endmodule
package my_package;
    timeunit 1ps;
    typedef enum {
        RED,
        GREEN,
        BLUE
    } color_e;
    typedef struct packed {
        logic [7:0] x;
        logic [7:0] y;
        color_e     color;
    } pixel_s;
    class MyPixelProcessor;
        rand pixel_s current_pixel;
        logic [15:0] processed_value;
        constraint valid_pixel {
            current_pixel.x inside {[0:255]};
            current_pixel.y inside {[0:255]};
        }
        function new();
            processed_value = 16'h0;
        endfunction
        function void process_pixel();
            processed_value = {current_pixel.x, current_pixel.y} + (current_pixel.color == RED ? 16'h100 : 16'h0);
        endfunction
    endclass
endpackage
module module_using_package (
    input  logic         sys_clk,
    input  my_package::color_e input_color,
    output my_package::pixel_s output_pixel_data
);
    import my_package::*;
    pixel_s internal_pixel;
    MyPixelProcessor processor_inst;
    initial begin
        processor_inst = new();
    end
    always_ff @(posedge sys_clk) begin
        internal_pixel.x <= internal_pixel.x + 1;
        internal_pixel.y <= internal_pixel.y + 2;
        internal_pixel.color <= input_color;
        output_pixel_data <= internal_pixel;
        void'(processor_inst.randomize());
        processor_inst.current_pixel = internal_pixel;
        processor_inst.process_pixel();
    end
endmodule
module module_top_dup (
    input  logic       clk,      
    input  logic [7:0] in_data,  
    output logic [15:0] out_sum, 
    input  int         param_in,
    output int         param_out
);
    logic [7:0] local_data;
    interface_my_bus i_bus_inst( .clk(clk) );
    interface_my_bus i_bus_array_inst[2]( {clk, clk} ); 
    module_with_interface_ports i_if_module (
        .sys_clk             (clk),
        .reset_n             (1'b1),
        .i_bus_master        (i_bus_inst.master),
        .o_bus_slave         (i_bus_inst.slave),
        .bus_array_ports     (i_bus_array_inst)
    );
    always_comb begin
        local_data = in_data + 1;
        out_sum = {local_data, in_data};
        param_out = param_in * 2;
    end
endmodule
module module_with_local_params (
    input  logic clk,
    input  logic [3:0] index_in,
    output logic [63:0] data_out
);
    localparam NUM_ELEMENTS = 8;
    localparam DATA_WIDTH   = 64;
    logic [DATA_WIDTH-1:0] data_array [NUM_ELEMENTS];
    initial begin
        for (int i=0; i<NUM_ELEMENTS; i++) begin
            data_array[i] = 64'hAAAA_BBBB_CCCC_DDDD + i;
        end
    end
    always_comb begin
        if (index_in < NUM_ELEMENTS) begin
            data_out = data_array[index_in];
        end else begin
            data_out = '0;
        end
    end
endmodule
module module_simple_array (
    input  logic         clk,
    input  logic [7:0]   in_byte,
    output logic [3:0]   out_nibbles [4], 
    output logic [15:0]  out_word_packed  
);
    logic [3:0] internal_nibbles [4];
    always_comb begin
        internal_nibbles[0] = in_byte[3:0];
        internal_nibbles[1] = in_byte[7:4];
        internal_nibbles[2] = 4'hA;
        internal_nibbles[3] = 4'h5;
        out_nibbles = internal_nibbles;
        out_word_packed = {in_byte, in_byte};
    end
endmodule
