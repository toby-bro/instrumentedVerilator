module tp_constructor_mod #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic                   clk,
    input  logic                   rst_n,
    input  logic [WIDTH-1:0]       in_data,
    output logic [WIDTH-1:0]       out_data
);
    logic [WIDTH-1:0] gen_array [DEPTH];
    generate
        genvar i;
        for (i = 0; i < DEPTH; i++) begin : G_INIT
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    gen_array[i] <= '0;
                end else begin
                    gen_array[i] <= in_data ^ (({WIDTH{1'b1}}) >> i);
                end
            end
        end
    endgenerate
    class accumulator;
        rand logic [WIDTH-1:0] value;
        function void add(logic [WIDTH-1:0] v);
            value += v;
        endfunction
    endclass
    always_ff @(posedge clk or negedge rst_n) begin
        accumulator acc;
        if (!rst_n) begin
            out_data <= '0;
            acc = new();
            acc.value = '0;
        end else begin
            acc = new();
            acc.value = gen_array[0];
            acc.add(gen_array[1]);
            out_data <= acc.value;
        end
    end
endmodule
module tp_destructor_mod #(
    parameter int WIDTH = 16
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [WIDTH-1:0]     a,
    output logic [WIDTH-1:0]     y
);
    typedef union packed {
        logic [WIDTH-1:0] word;
        struct packed {
            logic [WIDTH/2-1:0] lo;
            logic [WIDTH/2-1:0] hi;
        } parts;
    } data_u;
    data_u data_in;
    always_comb begin
        data_in.word = a;
        y = {data_in.parts.hi, data_in.parts.lo};
    end
    assert property (@(posedge clk) disable iff(!rst_n) y == {a[WIDTH/2-1:0], a[WIDTH-1:WIDTH/2]});
endmodule
module tp_enqueue_mod #(
    parameter int WIDTH = 8
) (
    input  logic                 clk,
    input  logic                 wr_en,
    input  logic [WIDTH-1:0]     wr_data,
    output logic [15:0]          q_size
);
    logic [WIDTH-1:0] job_q[$];
    always_ff @(posedge clk) begin
        if (wr_en) begin
            job_q.push_back(wr_data);
        end
        q_size <= job_q.size();
    end
endmodule
module tp_wait_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic pend_dec,
    input  logic pend_inc,
    output logic idle
);
    int pending_jobs;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pending_jobs <= 0;
        end else begin
            if (pend_inc) pending_jobs <= pending_jobs + 1;
            if (pend_dec && pending_jobs > 0) pending_jobs <= pending_jobs - 1;
        end
    end
    assign idle = (pending_jobs == 0);
endmodule
module tp_startWorker_mod (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  token_in,
    output logic [7:0]  token_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            token_out <= 8'h00;
        end else begin
            token_out <= token_in + 8'h1;
        end
    end
endmodule
module tp_workerJobLoop_mod #(
    parameter int WIDTH = 32
) (
    input  logic               clk,
    input  logic               rst_n,
    input  logic               job_valid,
    input  logic [WIDTH-1:0]   job_in,
    output logic [WIDTH-1:0]   job_out,
    output logic               done
);
    typedef enum logic [1:0] {IDLE, BUSY} state_e;
    state_e state;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state   <= IDLE;
            job_out <= '0;
            done    <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    if (job_valid) begin
                        job_out <= job_in ^ 32'hDEADBEEF;
                        state   <= BUSY;
                        done    <= 1'b0;
                    end
                end
                BUSY: begin
                    done  <= 1'b1;
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule
module tp_selfTest_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic [15:0] in_val,
    output logic [15:0] out_val
);
    logic [15:0] internal_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 16'h0;
            out_val      <= 16'h0;
        end else begin
            internal_reg <= in_val ^ 16'h00FF;
            out_val      <= internal_reg + 16'h0064;
        end
    end
endmodule
module threadscope_constructor_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic trig,
    output logic ready
);
    int counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            ready   <= 1'b0;
        end else begin
            if (trig) counter <= counter + 1;
            ready <= (counter == 0);
        end
    end
endmodule
module threadscope_enqueue_mod (
    input  logic           clk,
    input  logic           enq,
    input  logic [7:0]     payload,
    output logic [31:0]    depth
);
    logic [7:0] dynArray[$];
    always_ff @(posedge clk) begin
        if (enq) dynArray.push_back(payload);
        depth <= dynArray.size();
    end
endmodule
module threadscope_wait_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic busy_in,
    output logic idle_out
);
    logic busy_ff;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) busy_ff <= 1'b0;
        else        busy_ff <= busy_in;
    end
    assign idle_out = ~busy_ff;
endmodule
