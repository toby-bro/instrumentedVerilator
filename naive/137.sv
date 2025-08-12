module SimpleCombinationalLogic (
    input logic [7:0] data_in,
    input logic       op_sel,
    output logic [7:0] result_out
);
    parameter int C_ADD_OFFSET = 8;
    typedef enum logic [1:0] {
        OP_ADD = 2'b00,
        OP_SUB = 2'b01,
        OP_AND = 2'b10,
        OP_OR   = 2'b11
    } OperationType;
    typedef struct packed {
        logic [3:0] upper_nibble;
        logic [3:0] lower_nibble;
    } NibbleSplit_s;
    OperationType current_op;
    NibbleSplit_s split_data;
    logic [7:0] temp_result;
    always_comb begin
        if (op_sel == 1'b0) begin
            current_op = OP_ADD;
        end else begin
            current_op = OP_AND;
        end
        split_data.upper_nibble = data_in[7:4];
        split_data.lower_nibble = data_in[3:0];
        case (current_op)
            OP_ADD: temp_result = data_in + C_ADD_OFFSET;
            OP_SUB: temp_result = data_in - C_ADD_OFFSET;
            OP_AND: temp_result = data_in & ({split_data.upper_nibble, split_data.lower_nibble});
            OP_OR:  temp_result = data_in | ({split_data.upper_nibble, split_data.lower_nibble});
            default: temp_result = 8'hFF;
        endcase
    end
    assign result_out = temp_result;
endmodule
module DataStructureProcessor (
    input logic         clk,
    input logic         rst_n,
    input logic [1:0]   sel_idx,
    input logic [3:0]   val_in,
    input logic         push_en,
    input logic         pop_en,
    output logic [7:0]  array_out,
    output logic        queue_has_data,
    output logic        assoc_found
);
    parameter int STATIC_ARR_SIZE = 4;
    logic [7:0] packed_array [STATIC_ARR_SIZE];
    logic [3:0] unpacked_array [STATIC_ARR_SIZE];
    int         dyn_array[];
    int         my_queue[$];
    string      assoc_map[int];
    logic [7:0] current_array_val;
    logic       internal_assoc_found;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            packed_array <= '{default: 0};
            unpacked_array <= '{default: 0};
            dyn_array = new[0];
            my_queue = {};
            assoc_map.delete();
            current_array_val <= 0;
            internal_assoc_found <= 0;
            queue_has_data <= 0;
        end else begin
            packed_array[sel_idx] <= val_in;
            unpacked_array[sel_idx] <= val_in;
            if (push_en) begin
                dyn_array = new[dyn_array.size() + 1](dyn_array);
                dyn_array[dyn_array.size() - 1] = val_in;
                my_queue.push_back(val_in);
                assoc_map[val_in] = $sformatf("Value_%0d", val_in);
            end
            if (pop_en && my_queue.size() != 0) begin
                void'(my_queue.pop_front());
            end
            queue_has_data <= (my_queue.size() != 0);
            internal_assoc_found <= assoc_map.exists(val_in);
            current_array_val <= packed_array[sel_idx] + unpacked_array[sel_idx];
        end
    end
    assign array_out = current_array_val;
    assign assoc_found = internal_assoc_found;
endmodule
class BaseMultiplier;
    protected int base_value;
    local int temp_calc;
    function new(int init_val = 1);
        base_value = init_val;
    endfunction
    virtual function int multiply(int in_val);
        temp_calc = in_val * base_value;
        return temp_calc;
    endfunction
    function int get_base_value();
        return base_value;
    endfunction
endclass
class PowerMultiplier extends BaseMultiplier;
    protected int power_factor;
    function new(int init_val = 1, int p_factor = 2);
        super.new(init_val);
        power_factor = p_factor;
    endfunction
    virtual function int multiply(int in_val);
        int val = super.multiply(in_val);
        for (int i = 1; i < power_factor; i++) begin
            val *= in_val;
        end
        return val;
    endfunction
endclass
typedef union tagged {
    int   int_val;
    real  real_val;
    string str_val;
} DataVariant_u;
module ClassAndMethodHandler (
    input logic         clk,
    input logic         rst_n,
    input logic         enable_cls,
    input logic [7:0]   factor_in,
    output logic [15:0] class_result,
    output logic        class_valid
);
    BaseMultiplier my_base_obj;
    PowerMultiplier my_power_obj;
    BaseMultiplier polymorphic_obj;
    DataVariant_u data_union;
    logic [15:0] internal_result;
    logic        internal_valid;
    task automatic process_class_ops(BaseMultiplier obj, input int val, output int res);
        res = obj.multiply(val);
    endtask
    always_ff @(posedge clk or negedge rst_n) begin
        int res_val;
        int base_val_read;
        if (!rst_n) begin
            my_base_obj = null;
            my_power_obj = null;
            polymorphic_obj = null;
            internal_result <= 0;
            internal_valid <= 0;
            data_union.int_val = 0; 
        end else begin
            if (enable_cls) begin
                if (my_base_obj == null) begin
                    my_base_obj = new(5);
                end
                if (my_power_obj == null) begin
                    my_power_obj = new(2, 3);
                end
                if (factor_in[0] == 1'b0) begin
                    polymorphic_obj = my_base_obj;
                end else begin
                    polymorphic_obj = my_power_obj;
                end
                process_class_ops(polymorphic_obj, factor_in, res_val);
                internal_result <= res_val;
                base_val_read = my_base_obj.get_base_value();
                if (factor_in < 100) begin
                    data_union.int_val = (factor_in + base_val_read);
                end else begin
                    data_union.real_val = ($itor(factor_in) * 2.5);
                end
                internal_valid <= 1;
            end else begin
                internal_valid <= 0;
            end
        end
    end
    assign class_result = internal_result;
    assign class_valid = internal_valid;
endmodule
interface MyBusInterface;
    logic clk;
    logic rst_n;
    logic [7:0] bus_data;
    logic       bus_valid;
    logic       bus_ready;
    modport Master (input clk, input rst_n, output bus_data, output bus_valid, input bus_ready);
    modport Slave  (input clk, input rst_n, input bus_data, input bus_valid, output bus_ready);
endinterface
module InterfaceAndAssertionModule (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic                   bus_ready_in, 
    input  logic                   enable_gen,
    input  logic [7:0]             data_in,
    output logic [7:0]             processed_data,
    output logic                   assertion_triggered
);
    MyBusInterface bus_if_instance();
    assign bus_if_instance.clk     = clk;
    assign bus_if_instance.rst_n   = rst_n;
    assign bus_if_instance.bus_ready = bus_ready_in;
    logic [7:0] internal_processed_data;
    logic       internal_assertion_triggered = 0;
    assign bus_if_instance.bus_data  = data_in;
    assign bus_if_instance.bus_valid = enable_gen;
    let is_data_valid = (bus_if_instance.bus_valid && bus_if_instance.bus_ready);
    genvar i;
    generate
        if (1) begin : G_BLOCK_ONE
            always_comb begin
                if (is_data_valid) begin
                    internal_processed_data = bus_if_instance.bus_data + 1;
                end else begin
                    internal_processed_data = 8'h00;
                end
            end
        end
    endgenerate
    logic [7:0] bit_stream_val;
    logic       data_in_is_prime;
    always_comb begin
        bit_stream_val = {>>{data_in}};
        data_in_is_prime = (data_in inside {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97});
    end
    always_ff @(posedge bus_if_instance.clk) begin
        if (!bus_if_instance.rst_n) begin
            internal_assertion_triggered <= 0;
        end else begin
            if (bus_if_instance.bus_valid && !bus_if_instance.bus_ready && bus_if_instance.bus_data == 8'hAA) begin
                internal_assertion_triggered <= 1;
            end else begin
                internal_assertion_triggered <= 0;
            end
        end
    end
    property p_valid_ready_sequence;
        @(posedge bus_if_instance.clk) (bus_if_instance.bus_valid && bus_if_instance.rst_n) |-> ##[1:5] bus_if_instance.bus_ready;
    endproperty
    cover property (@(posedge bus_if_instance.clk) (is_data_valid && $rose(bus_if_instance.bus_valid)) |-> (bus_if_instance.bus_data > 0));
    assume property (@(posedge bus_if_instance.clk) bus_if_instance.bus_ready |-> !bus_if_instance.bus_valid);
    assign processed_data = internal_processed_data + bit_stream_val;
    assign assertion_triggered = internal_assertion_triggered;
endmodule
