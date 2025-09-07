module m_fork_control(
    input  logic       clk,
    input  logic       rst,
    output logic [3:0] counter
);
    event dummy_event;
    always_ff @(posedge clk or posedge rst) begin : main_proc
        if (rst) begin
            counter <= 4'd0;
        end else begin
            fork : fork_block
                counter <= counter + 4'd1;
                begin : branch2
                    counter <= counter + 4'd2;
                end
            join_none
            wait fork;          
            disable fork_block; 
        end
    end
endmodule
module m_wait_statement(
    input  logic clk,
    input  logic cond,
    output logic done
);
    always_ff @(posedge clk) begin
        if (!done) begin
            wait (cond); 
            done <= 1'b1;
        end
    end
endmodule
module m_intra_assign_event(
    input  logic clk,
    input  logic clk2,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= @(posedge clk2) d;
    end
endmodule
module m_named_event(
    input  logic clk,
    input  logic en,
    output logic outp
);
    event myEv;
    logic internal;
    always_ff @(posedge clk) begin
        if (en) begin
            internal <= 1'b1;
            -> myEv; 
        end
    end
    always @(myEv) begin
        outp = internal; 
    end
endmodule
module m_class_example(
    input  logic clk,
    input  logic in_sig,
    output logic [7:0] value
);
    class myClass;
        task automatic update(ref logic [7:0] v, input logic condition);
            wait (condition);   
            v = v + 8'h1;
        endtask
    endclass
    myClass c;
    always_ff @(posedge clk) begin
        if (c == null) begin
            c = new();
        end
        c.update(value, in_sig); 
    end
endmodule
