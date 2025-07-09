module lifetime_mod(input  logic in1, output logic out1);
    static int svalue = 42;
    always_comb begin
        automatic int temp = svalue + int'(in1);
        out1 = temp[0];
    end
endmodule
module net_mod(input logic in2, output logic out2);
    wire scalared [3:0] wvec;
    wire wdrv;
    assign wvec = {4{in2}};
    assign (strong1, weak0) wdrv = in2;
    always_comb out2 = wdrv;
endmodule
module function_formal_mod(input logic [7:0] data_in, output logic [7:0] data_out);
    function automatic void passthrough(input logic [7:0] din, output logic [7:0] dout_var);
        dout_var = din;
    endfunction
    function automatic int adder(const ref int lhs, const ref int rhs);
        adder = lhs + rhs;
    endfunction
    always_comb begin
        int lhs;
        int rhs;
        int dummy_sum;
        lhs = data_in;
        rhs = data_in;
        passthrough(data_in, data_out);
        dummy_sum = adder(lhs, rhs);
    end
endmodule
module loop_iterator_mod(input logic [3:0] dummy, output logic [3:0] result);
    always_comb begin
        automatic int sum;
        automatic int arr[0:3];
        sum = 0;
        for (int i = 0; i < 4; i++) begin
            automatic int local_i;
            local_i = i;
            arr[i] = local_i;
        end
        foreach (arr[j]) begin
            sum += arr[j];
        end
        result = sum[3:0];
    end
endmodule
module clocking_mod(input logic clk, input logic din, output logic dout);
    clocking cb @(posedge clk);
        input  din;
        output dout;
    endclocking
    always_comb begin
        dout = cb.din;
    end
endmodule
module class_proc_mod(input logic sig_in, output logic sig_out);
    class simple_c;
        int val;
        function new(int v = 0);
            val = v;
        endfunction
        function int get();
            return val;
        endfunction
    endclass
    always_comb begin
        automatic simple_c obj = new(int'(sig_in));
        sig_out = obj.get()[0];
    end
endmodule
