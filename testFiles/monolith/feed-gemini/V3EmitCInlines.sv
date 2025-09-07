module ModClassNew (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    class MyPacket;
        logic [7:0] payload;
        function new(logic [7:0] initial_payload);
            this.payload = initial_payload;
        endfunction
    endclass
    MyPacket pkt_h;
    always_comb begin
        pkt_h = new(in_data);
        out_data = pkt_h.payload;
    end
endmodule
module ModRandDistBiop (
    input bit clk,
    input bit reset_n,
    output logic [3:0] rand_val
);
    class MyRandClass;
        rand logic [3:0] value;
        constraint c_dist {
            value dist { 4 := 1, 5 := 2, 6 := 3 };
        }
    endclass
    MyRandClass rand_obj;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rand_val = 0;
            rand_obj = new();
        end else begin
            if (rand_obj.randomize()) begin
                rand_val = rand_obj.value;
            end else begin
                rand_val = 'x;
            end
        end
    end
endmodule
module ModRandDistTriop (
    input bit enable,
    input bit [1:0] selector,
    output logic [7:0] result_val
);
    class MyTriopRandClass;
        rand logic [7:0] item_val;
        constraint c_range_dist {
            item_val dist { [0:9]   :/ 1,
                             [10:19] :/ 2,
                             [20:29] :/ 3 };
        }
    endclass
    MyTriopRandClass triop_rand_obj;
    always_comb begin
        if (enable) begin
            if (triop_rand_obj == null) begin
                triop_rand_obj = new();
            end
            if (triop_rand_obj.randomize()) begin
                result_val = triop_rand_obj.item_val;
            end else begin
                result_val = 'x;
            end
        end else begin
            result_val = 0;
        end
    end
endmodule
