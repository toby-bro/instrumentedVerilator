`timescale 1ns/1ps
interface bus_if;
    logic req;
    logic gnt;
    modport master (input gnt, output req);
    modport slave  (input req, output gnt);
endinterface
module counter_struct_union #(parameter WIDTH = 16)
   (input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       in_data,
    output logic [WIDTH-1:0]       out_data);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } bytes_t;
    typedef union packed {
        bytes_t              s;
        logic [WIDTH-1:0]    word;
    } bytes_u;
    bytes_u reg_u;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) reg_u.word <= '0;
        else        reg_u.word <= in_data;
    end
    assign out_data = reg_u.word;
endmodule
module popcount_func #(parameter WIDTH = 32)
   (input  logic [WIDTH-1:0]                 vector_in,
    output logic [$clog2(WIDTH+1)-1:0]       count_out);
    function automatic int unsigned pop (input logic [WIDTH-1:0] v);
        int unsigned cnt;
        begin
            cnt = 0;
            for (int i = 0; i < WIDTH; i++) cnt += v[i];
            return cnt;
        end
    endfunction
    assign count_out = pop(vector_in);
endmodule
module generate_example #(parameter N = 4)
   (input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus);
    generate
        for (genvar i = 0; i < N; i++) begin : gen_blk
            always_comb begin
                out_bus[i] = ~in_bus[i];
            end
        end
    endgenerate
endmodule
module enum_case_module
   (input  logic [1:0] in_sel,
    output logic [3:0] out_val);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2, ERR = 2'd3} state_e;
    state_e state;
    always_comb begin
        state = state_e'(in_sel);
        unique case (state)
            IDLE : out_val = 4'h0;
            RUN  : out_val = 4'hA;
            DONE : out_val = 4'hF;
            default: out_val = 4'h5;
        endcase
    end
endmodule
module class_usage_module
   (input  logic       in_flag,
    output logic [7:0] out_value);
    class simple_class;
        rand bit [7:0] val;
        function void post_randomize();
            val = val ^ 8'hFF;
        endfunction
        function automatic bit [7:0] get();
            return val;
        endfunction
    endclass
    always_comb begin
        simple_class obj = new();      
        void'(obj.randomize());
        if (in_flag)  out_value = obj.get();
        else          out_value = 8'h00;
    end
endmodule
module assertion_module
   (input  logic clk,
    input  logic sig_in,
    output logic dummy_out);
    property p_stable;
        @(posedge clk) sig_in |=> sig_in;
    endproperty
    assert_sig_stable: assert property (p_stable);
    assign dummy_out = sig_in;
endmodule
module covergroup_module
   (input  logic       clk,
    input  logic [3:0] data,
    output logic [3:0] data_mirror);
    covergroup cg @(posedge clk);
        coverpoint data;
    endgroup
    cg cov;
    always_ff @(posedge clk) begin
        if (cov == null) cov = new();  
        cov.sample();
        data_mirror <= data;
    end
endmodule
module interface_module
   (bus_if            b,
    input  logic      ctrl,
    output logic      status);
    assign b.req = ctrl;
    assign status = b.gnt;
endmodule
