interface bus_if #(parameter WIDTH = 8);
    logic [WIDTH-1:0] data;
    logic             valid;
endinterface
module graph_long_path (input  logic [7:0] in,
                        output logic [7:0] out);
    logic [7:0] a1, a2, a3, a4, a5, a6, a7;
    always_comb begin
        a1 = in + 8'd1;
        a2 = {a1[6:0], a1[7]};
        a3 = a2 ^ 8'hAA;
        a4 = ~a3;
        a5 = a4 + 8'd5;
        a6 = a5 >> 1;
        a7 = a6 | 8'h55;
        out = a7;
    end
endmodule
module graph_branch (input  logic x,
                     input  logic y,
                     output logic z);
    logic n1, n2, n3, n4;
    always_comb begin
        n1 = x & y;
        n2 = x | y;
        n3 = n1 ^ n2;
        n4 = ~(n3 & y);
        z  = n4;
    end
endmodule
module graph_function (input  logic [15:0] din,
                       output logic [15:0] dout);
    function automatic [15:0] f1 (input [15:0] a);
        f1 = a + 16'h0001;
    endfunction
    function automatic [15:0] f2 (input [15:0] a);
        f2 = f1(a) ^ 16'hA5A5;
    endfunction
    always_comb begin
        dout = f2(din);
    end
endmodule
module graph_task (input  logic clk,
                   input  logic rst,
                   input  logic in_sig,
                   output logic out_sig);
    logic tmp1, tmp2;
    task automatic t1 (input  logic i,
                       output logic o);
        o = ~i;
    endtask
    task automatic t2 (input  logic i,
                       output logic o);
        logic tmp_local;
        t1(i, tmp_local);
        o = i & tmp_local;
    endtask
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            tmp1 <= 1'b0;
            tmp2 <= 1'b0;
        end else begin
            t2(in_sig, tmp1);
            tmp2 <= tmp1;
        end
    end
    assign out_sig = tmp2;
endmodule
module graph_generate #(parameter WIDTH = 8)
                       (input  logic [WIDTH-1:0] in_vec,
                        output logic [WIDTH-1:0] out_vec);
    genvar i;
    for (i = 0; i < WIDTH; i = i + 1) begin : GEN_BLOCK
        assign out_vec[i] = in_vec[i] ^ (i % 2);
    end
endmodule
module graph_array_slice (input  logic [3:0][7:0] in_bus,
                          output logic [7:0]       sum_low,
                          output logic [7:0]       sum_high);
    logic [3:0][7:0] buffer;
    always_comb begin
        buffer = in_bus;
    end
    assign sum_low  = buffer[0] + buffer[1];
    assign sum_high = buffer[2] + buffer[3];
endmodule
module graph_enum (input  logic clk,
                   input  logic rst,
                   input  logic sel,
                   output logic done);
    typedef enum logic [1:0] {IDLE = 2'd0, RUN = 2'd1, FINISH = 2'd2} state_t;
    state_t state, next_state;
    always_comb begin
        case (state)
            IDLE:   next_state = sel ? RUN   : IDLE;
            RUN:    next_state = sel ? RUN   : FINISH;
            FINISH: next_state = sel ? IDLE  : FINISH;
            default: next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst) state <= IDLE;
        else     state <= next_state;
    end
    assign done = (state == FINISH);
endmodule
module graph_struct (input  logic       clk,
                     input  logic       rst,
                     input  logic [7:0] in_data,
                     output logic [7:0] out_data);
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } pair_t;
    pair_t s1;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            s1.a <= 8'h00;
            s1.b <= 8'h00;
        end else begin
            s1.a <= in_data;
            s1.b <= s1.a + 8'h01;
        end
    end
    assign out_data = s1.b;
endmodule
module graph_interface_user (input  logic       clk,
                             input  logic [7:0] data_in,
                             input  logic       valid_in,
                             output logic       parity,
                             output logic       valid_out);
    bus_if ifc();
    always_comb begin
        ifc.data  = data_in;
        ifc.valid = valid_in;
    end
    assign parity = ^ifc.data;
    always_ff @(posedge clk) begin
        valid_out <= ifc.valid;
    end
endmodule
module graph_transitive (input  logic a,
                         input  logic b,
                         input  logic c,
                         output logic y);
    logic n1, n2, n3, n4, n5;
    assign n1 = a & b;
    assign n2 = b & c;
    assign n3 = a | c;
    assign n4 = n1 & n3;
    assign n5 = n2 | n4;
    assign y  = n5;
endmodule
