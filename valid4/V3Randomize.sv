module BasicRandomization (
    input logic req_i,
    input int     seed_i,
    output logic  done_o,
    output int    random_val_o
);
    class MyBasicRandClass;
        rand int my_int_rand;
        rand bit my_bit_rand;
        function new();
        endfunction
        function void pre_randomize();
        endfunction
        function void post_randomize();
        endfunction
        constraint basic_c {
            my_int_rand inside {[1:100]};
            my_bit_rand == 1'b1;
        }
    endclass
    MyBasicRandClass inst;
    always_comb begin
        done_o = 1'b0;
        random_val_o = 0;
        if (req_i) begin
            inst = new();
            inst.srandom(seed_i);
            void'(inst.randomize());
            inst.my_int_rand.rand_mode(0);
            inst.rand_mode(1);
            inst.basic_c.constraint_mode(0);
            inst.constraint_mode(1);
            random_val_o = inst.my_int_rand;
            done_o = 1'b1;
        end
    end
endmodule
module ComplexRandomData (
    input logic req_i,
    output logic done_o,
    output int   first_val_o
);
    typedef enum {RED, GREEN, BLUE} color_e;
    class NestedRandClass;
        rand int nested_id;
        constraint nested_id_c { nested_id > 0; };
        function new(); endfunction
    endclass
    class MyComplexRandClass;
        randc int randc_int_var;
        randc color_e randc_enum_var;
        rand struct packed {
            logic [7:0] field_a;
            int         field_b;
        } packed_struct_rand;
        rand struct {
            rand int sub_field1;
            int sub_field2;
        } unpacked_struct_rand;
        rand union packed {
            int u_int_val;
            logic [31:0] u_logic_val;
        } packed_union_rand;
        rand NestedRandClass nested_obj;
        rand int dyn_array_rand[];
        rand int assoc_array_rand[string];
        rand int queue_rand[$];
        rand int my_int_rand;
        rand bit my_bit_rand;
        const string my_key_for_assoc = "key1";
        const string my_key_for_assoc_exists = "key2";
        function new();
            nested_obj = new();
        endfunction
        constraint complex_c {
            randc_int_var inside {[1:10]};
            randc_enum_var inside {RED, BLUE};
            packed_struct_rand.field_a == 8'hFF;
            packed_struct_rand.field_b inside {[10:20]};
            unpacked_struct_rand.sub_field1 > 5;
            packed_union_rand.u_int_val < 100;
            dyn_array_rand.size() inside {[1:5]};
            foreach (dyn_array_rand[i]) {
                dyn_array_rand[i] > 0;
            }
            foreach (dyn_array_rand[i]) dyn_array_rand[i] inside {10, 20, 30};
            queue_rand.size() < 10;
            foreach (queue_rand[j]) {
                queue_rand[j] % 2 == 0;
            }
            assoc_array_rand[my_key_for_assoc] inside {[1:50]};
            assoc_array_rand.exists(my_key_for_assoc_exists);
            nested_obj.nested_id < 1000;
        }
        constraint operator_c {
            (randc_int_var + nested_obj.nested_id) > 10 && (randc_int_var - nested_obj.nested_id) < 50;
            my_int_rand == 0;
            (my_bit_rand) ? (my_int_rand < 30) : (my_int_rand != 25);
            randc_int_var == {32{my_bit_rand}};
            packed_struct_rand.field_a[7:0] == 8'hAA;
        }
        constraint before_unique_c {
            solve dyn_array_rand before queue_rand;
            unique {dyn_array_rand, queue_rand};
        }
    endclass
    MyComplexRandClass inst_complex;
    always_comb begin
        done_o = 1'b0;
        first_val_o = 0;
        if (req_i) begin
            inst_complex = new();
            inst_complex.dyn_array_rand = new[3];
            inst_complex.queue_rand = {1,2,3};
            inst_complex.assoc_array_rand = '{"key1": 10};
            void'(inst_complex.randomize());
            void'(inst_complex.randomize() with {
                inst_complex.randc_int_var > 5;
                inst_complex.packed_struct_rand.field_a < 200;
                inst_complex.dyn_array_rand.size() == 3;
                inst_complex.my_int_rand == (10 + 20);
            });
            first_val_o = inst_complex.randc_int_var;
            done_o = 1'b1;
        end
    end
endmodule
module ErrorTrigger (
    input logic req_i,
    output logic done_o
);
    class RandModeConstraintModeCalls;
        rand logic [7:0] unpacked_array_member[4];
        rand struct packed {int val;} packed_struct_member;
        typedef struct {
            rand int u_s_member;
        } MyUnpackedStruct;
        MyUnpackedStruct my_unpacked_struct_instance;
        rand int dynamic_array_member[];
        rand int normal_rand_member;
        constraint normal_con { normal_rand_member > 0; }
        function new();
            dynamic_array_member = new[2];
        endfunction
        function void perform_rand_mode_calls();
            void'(unpacked_array_member.rand_mode(0));
            void'(unpacked_array_member.rand_mode(1));
            void'(dynamic_array_member.rand_mode(0));
            void'(dynamic_array_member.rand_mode(1));
            void'(normal_rand_member.rand_mode(0));
            void'(normal_rand_member.rand_mode(1));
            void'(normal_con.constraint_mode(0));
            void'(normal_con.constraint_mode(1));
            void'(this.rand_mode(0));
            void'(this.rand_mode(1));
            void'(this.constraint_mode(0));
            void'(this.constraint_mode(1));
        endfunction
    endclass
    RandModeConstraintModeCalls calls_inst;
    always_comb begin
        done_o = 1'b0;
        if (req_i) begin
            calls_inst = new();
            calls_inst.perform_rand_mode_calls();
            void'(calls_inst.randomize());
            done_o = 1'b1;
        end
    end
endmodule
module RandCaseExample (
    input logic req_i,
    output logic done_o,
    output int rand_case_output_o
);
    class MyRandCaseClass;
        rand int choice_weight_1;
        rand int choice_weight_2;
        rand int choice_weight_0;
        rand int selected_value;
        constraint weights_c {
            choice_weight_1 inside {[1:10]};
            choice_weight_2 inside {[1:10]};
            choice_weight_0 == 0;
        }
        function new();
        endfunction
        function void do_randcase();
            randcase
                choice_weight_1 : selected_value = 10;
                choice_weight_2 : selected_value = 20;
                choice_weight_0 : selected_value = 0;
            endcase
        endfunction
    endclass
    MyRandCaseClass inst_randcase;
    always_comb begin
        done_o = 1'b0;
        rand_case_output_o = 0;
        if (req_i) begin
            inst_randcase = new();
            void'(inst_randcase.randomize());
            inst_randcase.do_randcase();
            rand_case_output_o = inst_randcase.selected_value;
            done_o = 1'b1;
        end
    end
endmodule
