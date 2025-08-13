module prepost_expr_mod (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter  <= 8'd0;
            out_data <= 8'd0;
        end else begin
            out_data <= (++counter) + in_data; 
        end
    end
endmodule
module poststmt_mod (
    input  logic      clk,
    input  logic      en,
    output logic [3:0] q
);
    logic [3:0] idx;
    always_ff @(posedge clk) begin
        if (!en) begin
            idx <= 4'd0;
        end else begin
            idx++;                           
        end
        q <= idx;
    end
endmodule
module array_sel_inc_mod (
    input  logic       clk,
    input  logic [2:0] addr_in,
    output logic [7:0] value_out
);
    logic [7:0] mem [0:7];
    logic [2:0] ptr;
    always_ff @(posedge clk) begin
        ptr <= addr_in;
        mem[ptr++]++;                       
        value_out <= mem[ptr];
    end
endmodule
module decrements_mod (
    input  logic       clk,
    input  logic [3:0] start_val,
    output logic [3:0] result
);
    logic [3:0] val;
    always_ff @(posedge clk) begin
        val <= start_val;
        --val;                              
        result <= val;
    end
endmodule
module foreach_while_mod (
    input  logic [15:0] data_in,
    output logic [4:0]  bitcount
);
    function automatic int count_bits(input logic [15:0] val);
        int idx;
        int c;
        c = 0;
        foreach (val[idx]) begin
            if (val[idx]) c++;
        end
        while (val != 0) begin
            c  = c + (val & 1);
            val = val >> 1;
        end
        return c;
    endfunction
    assign bitcount = count_bits(data_in);
endmodule
module task_mod (
    input  logic clk,
    input  logic start,
    output logic done
);
    logic [7:0] acc;
    task automatic accumulate(input int n);
        int j;
        j = 0;
        while (j < n) begin
            acc += j;
            j++;
        end
        acc++;                              
    endtask
    always_ff @(posedge clk) begin
        if (start) begin
            accumulate(4);
        end
        done <= start;
    end
endmodule
module case_mod (
    input  logic [1:0] sel,
    input  logic       clk,
    output logic [3:0] out
);
    logic [3:0] a;
    logic [3:0] b;
    always_ff @(posedge clk) begin
        case (sel)
            2'd0: begin
                out <= ++a;                 
            end
            2'd1: begin
                b--;                        
                out <= b;
            end
            default: out <= 4'd0;
        endcase
    end
endmodule
module wait_mod (
    input  logic clk,
    input  logic trigger,
    output logic done
);
    logic flag;
    always_ff @(posedge clk) begin : wait_block
        if (trigger) begin
            flag <= 1'b1;
            wait (flag == 1'b0);            
        end else begin
            flag <= 1'b0;
        end
        done <= flag;
    end
endmodule
module event_ctrl_mod (
    input  logic clk,
    input  logic go,
    output logic [7:0] count
);
    event ev;
    logic [7:0] c;
    always_ff @(posedge clk) begin
        if (go) -> ev;                      
    end
    always @(ev) begin
        c++;                                
    end
    assign count = c;
endmodule
module gen_mod (
    input  logic [3:0] in_bus,
    output logic [3:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < 4; i = i + 1) begin : gen_loop
            assign out_bus[i] = in_bus[i];
        end
    endgenerate
endmodule
module logical_mod (
    input  logic clk,
    input  logic a_in,
    input  logic b_in,
    output logic outp
);
    logic a;
    logic b;
    logic x;
    always_ff @(posedge clk) begin
        a <= a_in;
        b <= b_in;
        if (a && b++) begin                 
            x <= 1'b1;
        end else if (a || --x) begin        
            x <= 1'b0;
        end
        outp <= x;
    end
endmodule
