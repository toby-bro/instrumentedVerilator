module RandomizeSimple (
    input bit clk,
    input bit reset_n,
    input int srandom_seed, 
    output logic [7:0] out_val_a,
    output logic [7:0] out_val_b,
    output logic [7:0] out_val_c
);
    class MySimpleRandomizable;
        rand logic [7:0] rand_var_a;
        randc logic [7:0] randc_var_b; 
        function void pre_randomize();
        endfunction
        function void post_randomize();
        endfunction
        function void srandom(int seed);
        endfunction
    endclass
    MySimpleRandomizable inst;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            inst = null;
            out_val_a = 0;
            out_val_b = 0;
            out_val_c = 0;
        end else begin
            if (inst == null) begin
                inst = new();
                inst.srandom(srandom_seed); 
            end
            void'(inst.randomize());
            out_val_a = inst.rand_var_a;
            out_val_b = inst.randc_var_b;
            out_val_c = inst.rand_var_a + inst.randc_var_b; 
        end
    end
endmodule
module RandomizeWithConstraints (
    input bit clk,
    input bit enable_random,
    output logic [3:0] x_out,
    output logic [3:0] y_out,
    output logic [3:0] sum_out
);
    class MyConstrainedRandomizable;
        rand int x;
        rand int y;
        constraint c_xy {
            x inside {[1:10]}; 
            y > x;             
            y < 15;            
            (x + y) < 20;      
            if (x % 2 == 0) {  
                y % 2 == 0;
            } else {
                y % 2 == 1;
            }
        }
    endclass
    MyConstrainedRandomizable constrained_inst;
    always_ff @(posedge clk) begin
        if (constrained_inst == null) begin
            constrained_inst = new();
        end
        if (enable_random) begin
            void'(constrained_inst.randomize() with {
                x inside {[1:5]}; 
                y >= 2;
                y <= 10;
            });
        end
        x_out = constrained_inst.x;
        y_out = constrained_inst.y;
        sum_out = constrained_inst.x + constrained_inst.y;
    end
endmodule
module RandModeAndConstraintMode (
    input bit clk,
    input bit set_mode_inst,
    input bit set_mode_var,
    output logic [3:0] addr,
    output logic [7:0] data,
    output logic [7:0] reg_val_out
);
    class MyModeTest;
        rand logic [3:0] address;
        rand logic [7:0] datum;
        constraint c_addr_data {
            address < 10;
            datum > 10;
        }
        rand logic [7:0] my_register;
        constraint c_my_register {
            my_register inside {[0:100]};
        }
    endclass
    MyModeTest mode_inst;
    always_ff @(posedge clk) begin
        if (mode_inst == null) begin
            mode_inst = new();
        end
        if (set_mode_inst) begin
            void'(mode_inst.rand_mode(1)); 
            void'(mode_inst.c_addr_data.constraint_mode(0)); 
        end else begin
            void'(mode_inst.rand_mode(0)); 
            void'(mode_inst.c_addr_data.constraint_mode(1)); 
        end
        if (set_mode_var) begin
            void'(mode_inst.datum.rand_mode(0)); 
            void'(mode_inst.c_my_register.constraint_mode(1)); 
        end else begin
            void'(mode_inst.datum.rand_mode(1)); 
            void'(mode_inst.c_my_register.constraint_mode(0)); 
        end
        void'(mode_inst.randomize());
        addr = mode_inst.address;
        data = mode_inst.datum;
        reg_val_out = mode_inst.my_register;
    end
endmodule
module ComplexRandTypes (
    input bit clk,
    input bit trigger_rand,
    output logic [3:0] s_out,
    output logic [7:0] arr_out_0,
    output logic [7:0] q_out_0,
    output logic [7:0] assoc_out_idx1,
    output logic [1:0] enum_out,
    output logic [7:0] replicated_val_out,
    output logic bit bit_select_val_out
);
    typedef enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} MyState_e;
    class ComplexRandTest;
        rand struct packed { 
            logic [3:0] value;
            logic enable;
        } my_packed_struct;
        rand logic [7:0] unpacked_arr [2]; 
        rand int dyn_arr[]; 
        rand byte my_queue[$]; 
        rand int my_assoc_arr[string]; 
        randc MyState_e current_state; 
        rand logic [7:0] replicate_val; 
        rand logic [7:0] bit_select_val; 
        constraint c_complex {
            my_packed_struct.value inside {[0:15]};      
            unpacked_arr[0] > unpacked_arr[1];           
            dyn_arr.size() == 5;                         
            my_queue.size() inside {[1:3]};              
            foreach (dyn_arr[i]) {                       
                dyn_arr[i] > 0;
            }
            foreach (my_queue[j]) {                      
                my_queue[j] % 2 == 0;
            }
            my_assoc_arr.exists("key1");                 
            my_assoc_arr["key1"] inside {[10:20]};       
            current_state != STATE_IDLE;                 
            replicate_val == {8{1'b1}};                  
            bit_select_val[0] == 1'b0;                   
            bit_select_val[7:4] == 4'b1010;              
        }
        constraint c_unsupported {
            unique {my_packed_struct.value, unpacked_arr};
            my_packed_struct.value before unpacked_arr[0];
        }
        function void new();
            super.new();
            dyn_arr = new[0]; 
            my_queue = {}; 
        endfunction
    endclass
    ComplexRandTest complex_inst;
    always_ff @(posedge clk) begin
        if (complex_inst == null) begin
            complex_inst = new();
        end
        if (trigger_rand) begin
            void'(complex_inst.randomize());
        end
        s_out = complex_inst.my_packed_struct.value;
        arr_out_0 = complex_inst.unpacked_arr[0];
        q_out_0 = complex_inst.my_queue.size() > 0 ? complex_inst.my_queue[0] : 0;
        assoc_out_idx1 = complex_inst.my_assoc_arr.exists("key1") ? complex_inst.my_assoc_arr["key1"] : 0;
        enum_out = complex_inst.current_state;
        replicated_val_out = complex_inst.replicate_val;
        bit_select_val_out = complex_inst.bit_select_val[0];
    end
endmodule
module RandCaseExample (
    input bit clk,
    input bit reset,
    output logic [3:0] rand_val
);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            rand_val = 0;
        end else begin
            randcase
                10 : rand_val = 1;
                20 : rand_val = 2;
                30 : rand_val = 3;
                0  : rand_val = 4; 
                default: rand_val = 15; 
            endcase
        end
    end
endmodule
module InheritanceAndStatic (
    input bit clk,
    input bit enable_rand_base,
    output logic [7:0] base_val_out,
    output logic [7:0] derived_val_out,
    output logic [7:0] static_val_out
);
    class BaseClass;
        rand logic [7:0] base_var;
        static rand int static_rand_var; 
        constraint c_base {
            base_var inside {[0:200]};
        }
        static constraint c_static { 
            static_rand_var > 0;
        }
        function void new();
            super.new();
            void'(static_rand_var.rand_mode(1));
            void'(c_static.constraint_mode(1));
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        rand logic [7:0] derived_var;
        constraint c_derived {
            derived_var > base_var;
        }
    endclass
    BaseClass base_inst;
    DerivedClass derived_inst;
    always_ff @(posedge clk) begin
        if (base_inst == null) begin
            base_inst = new();
            derived_inst = new();
        end
        if (enable_rand_base) begin
            void'(base_inst.randomize()); 
        end else begin
            void'(derived_inst.randomize() with {
                derived_var inside {[10:250]};
                BaseClass::static_rand_var > 100; 
            });
        end
        base_val_out = base_inst.base_var;
        derived_val_out = derived_inst.derived_var;
        static_val_out = BaseClass::static_rand_var;
    end
endmodule
module StdRandomize (
    input bit clk,
    input bit trigger,
    output logic [31:0] std_rand_out1,
    output logic [31:0] std_rand_out2
);
    rand int module_rand_var1;
    rand int module_rand_var2;
    always_ff @(posedge clk) begin
        if (trigger) begin
            void'(std::randomize(module_rand_var1, module_rand_var2));
        end
        std_rand_out1 = module_rand_var1;
        std_rand_out2 = module_rand_var2;
    end
endmodule
module CountOnesTest (
    input bit clk,
    input bit do_randomize,
    output logic [7:0] val_out,
    output logic [3:0] ones_out
);
    class MyCountOnesClass;
        rand logic [7:0] my_val;
        constraint c_count_ones {
            $countones(my_val) > 4; 
            $countones(my_val) < 8;
        }
    endclass
    MyCountOnesClass count_ones_inst;
    always_ff @(posedge clk) begin
        if (count_ones_inst == null) begin
            count_ones_inst = new();
        end
        if (do_randomize) begin
            void'(count_ones_inst.randomize());
        end
        val_out = count_ones_inst.my_val;
        ones_out = $countones(count_ones_inst.my_val);
    end
endmodule
