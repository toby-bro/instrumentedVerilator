module m_shadow_var (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  q
);
    always_ff @(posedge clk) begin
        q <= din;
    end
endmodule
module m_flag_shared (
    input  logic        clk,
    input  logic [7:0]  din0,
    input  logic [7:0]  din1,
    input  logic [1:0]  idx0,
    input  logic [1:0]  idx1,
    output logic [7:0]  dout
);
    typedef logic [7:0] byte_t;
    byte_t mem [0:3];
    always_ff @(posedge clk) begin
        mem[idx0] <= din0;
        mem[idx1] <= din1;
    end
    assign dout = mem[idx0];
endmodule
module m_value_queue_whole (
    input  logic              clk,
    input  logic [7:0]        din [0:3],
    output logic [9:0]        sum
);
    typedef logic [7:0] byte_t;
    byte_t arr [0:3];
    always_ff @(posedge clk) begin
        for (int i = 0; i < 4; i++) begin
            arr[i] <= din[i];
        end
    end
    always_comb begin
        sum = 0;
        for (int i = 0; i < 4; i++) begin
            sum += arr[i];
        end
    end
endmodule
module m_value_queue_partial (
    input  logic        clk,
    input  logic [3:0]  nibble,
    output logic [7:0]  first_elem
);
    typedef logic [7:0] byte_t;
    byte_t array_p [0:3];
    always_ff @(posedge clk) begin
        for (int i = 0; i < 4; i++) begin
            array_p[i][3:0] <= nibble;
        end
    end
    assign first_elem = array_p[0];
endmodule
module m_flag_unique (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  q
);
    logic [7:0] q_reg;
    logic       dummy;
    always_ff @(posedge clk) fork
        begin
            q_reg <= din;
        end
        begin
            dummy <= ~dummy;
        end
    join_any
    assign q = q_reg;
endmodule
module m_event_fire (
    input  logic  clk,
    input  logic  trigger,
    output logic  fired
);
    event ev;
    logic flag;
    always_ff @(posedge clk) begin
        if (trigger) -> ev;
    end
    always @(ev) begin
        flag <= 1'b1;
    end
    assign fired = flag;
endmodule
