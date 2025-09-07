module isolate_simple (input  logic        clk,
                       input  logic [7:0]  din,
                       output logic [7:0]  dout);
    (* isolate_assignments *) logic [7:0] iso;
    logic [7:0] other;
    function automatic [7:0] incr (input [7:0] v);
        incr = v + 8'h1;
    endfunction
    always_ff @(posedge clk) begin
        if (din[0]) begin
            iso   <= incr(din);
            other <= din;
        end else begin
            other <= iso;
            iso   <= other;
        end
    end
    assign dout = iso ^ other;
endmodule
module isolate_func (input  logic         clk,
                     input  logic         en,
                     input  logic [31:0]  a,
                     output logic [31:0]  y);
    (* isolate_assignments *) logic [31:0] target;
    logic [31:0] tmp;
    function automatic [31:0] mix (input [31:0] v1, input [31:0] v2);
        mix = (v1 ^ v2) + v1;
    endfunction
    always_ff @(posedge clk) begin
        if (en) begin
            target <= mix(a, tmp);
        end
        tmp <= target + a;
    end
    assign y = target & tmp;
endmodule
module isolate_loop (input  logic        clk,
                     input  logic        rst_n,
                     input  logic [3:0]  inp,
                     output logic [3:0]  accum);
    (* isolate_assignments *) logic [3:0] counter;
    logic [3:0] sum;
    integer i;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            counter <= 0;
            sum     <= 0;
        end else begin
            for (i = 0; i < 4; i = i + 1) begin
                if (inp[i]) begin
                    counter <= counter + 1;
                end else begin
                    sum <= sum + i[3:0];
                end
            end
        end
    end
    assign accum = counter + sum;
endmodule
module isolate_multi (input  logic        clk,
                      input  logic [7:0]  din,
                      output logic [15:0] dout);
    (* isolate_assignments *) logic [7:0] isoA;
    (* isolate_assignments *) logic [7:0] isoB;
    logic [15:0] red;
    always_ff @(posedge clk) begin
        isoA <= din;
        isoB <= ~din;
        red  <= isoA + isoB;
    end
    assign dout = red;
endmodule
module isolate_expr_stmt (input  logic        clk,
                          input  logic [7:0]  din,
                          output logic [7:0]  outp);
    (* isolate_assignments *) logic [7:0] isoVal;
    task automatic modify (ref logic [7:0] v);
        v = v + 8'h5;
    endtask
    function automatic [7:0] dec (input [7:0] v);
        dec = v - 1;
    endfunction
    always_ff @(posedge clk) begin
        isoVal <= dec(din);
        modify(isoVal);               
    end
    assign outp = isoVal;
endmodule
module isolate_array (input  logic        clk,
                      input  logic [1:0]  idx,
                      input  logic [3:0]  val,
                      output logic [3:0]  out);
    (* isolate_assignments *) logic [3:0] mem [0:3];
    always_ff @(posedge clk) begin
        mem[idx] <= val;
    end
    assign out = mem[idx];
endmodule
