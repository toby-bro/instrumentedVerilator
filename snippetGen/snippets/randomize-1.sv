module top (
    input bit GGGin,
    output bit GGGout
);

    //INJECT

    typedef enum { GGG_A, GGG_B, GGG_C } GGG_state_enum; //INJECT

    class GGG_my_class;
        rand int GGG_a; //INJECT
        randc GGG_state_enum GGG_state; //INJECT

        virtual function int randomize();
            // Placeholder, will be replaced by Verilator //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_my_class GGG_inst; //INJECT

    always @(posedge GGGin) begin
        // Instance creation needed for linting simulation flow
        if (GGG_inst == null) begin
            GGG_inst = new(); // INJECT
        end
        GGGout = GGG_inst.randomize(); //INJECT
    end

    //INJECT

endmodule

module GGG_class_rand_modes (
    input bit GGGin,
    output logic [7:0] GGGout
);

    //INJECT

    class GGG_mode_class; //INJECT
        rand int GGG_var1; //INJECT
        rand bit [3:0] GGG_var2; //INJECT

        constraint GGG_constr1 { GGG_var1 > 10; } //INJECT
        constraint GGG_constr2 { GGG_var2 != GGG_var1; } //INJECT

        virtual function int randomize();
            // Placeholder //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_mode_class GGG_mode_inst; //INJECT

    always @(posedge GGGin) begin
        // Instance creation needed for linting simulation flow
        if (GGG_mode_inst == null) begin
            GGG_mode_inst = new(); // INJECT
        end
        void'(GGG_mode_inst.rand_mode(0)); // Turn all rand off //INJECT
        void'(GGG_mode_inst.GGG_var1.rand_mode(1)); // Turn one on //INJECT
        void'(GGG_mode_inst.constraint_mode(0)); // Turn all constraints off //INJECT
        void'(GGG_mode_inst.GGG_constr1.constraint_mode(1)); // Turn one on //INJECT

        void'(GGG_mode_inst.randomize()); //INJECT

        GGGout = GGG_mode_inst.GGG_var1[7:0]; //INJECT
    end

    //INJECT

endmodule

module GGG_inline_constraints (
    input bit GGGin,
    output int GGGout
);

    //INJECT

    class GGG_inline_class; //INJECT
        rand int GGG_x; //INJECT
        rand int GGG_y; //INJECT

        virtual function int randomize();
            // Placeholder //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_inline_class GGG_inline_inst; //INJECT

    always @(posedge GGGin) begin
        // Instance creation needed for linting simulation flow
         if (GGG_inline_inst == null) begin
            GGG_inline_inst = new(); // INJECT
        end
        // randomize with inline constraints //INJECT
        void'(GGG_inline_inst.randomize() with { //INJECT
            GGG_x > GGG_y; //INJECT
            GGG_y inside { [0:10], 20 }; //INJECT
            GGG_x + GGG_y < 50; //INJECT
        }); //INJECT

        GGGout = GGG_inline_inst.GGG_x + GGG_inline_inst.GGG_y; //INJECT
    end

    //INJECT

endmodule

module GGG_structured_types_rand (
    input bit GGGin,
    output logic [15:0] GGGout
);

    //INJECT

    class GGG_structured_class; //INJECT
        typedef struct packed { //INJECT
            bit [3:0] GGG_f1; //INJECT
            bit [3:0] GGG_f2; //INJECT
        } GGG_packed_s; //INJECT

        typedef bit [7:0] GGG_unpacked_a [2]; //INJECT
        typedef int GGG_queue []; //INJECT
        typedef string GGG_assoc_a [string]; //INJECT

        rand GGG_packed_s GGG_ps; //INJECT
        rand GGG_unpacked_a GGG_ua; //INJECT
        rand GGG_queue GGG_q; //INJECT
        rand GGG_assoc_a GGG_aa; //INJECT

        virtual function int randomize();
            // Placeholder //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_structured_class GGG_struct_inst; //INJECT

    always @(posedge GGGin) begin
        // Instance creation needed for linting simulation flow
        if (GGG_struct_inst == null) begin
            GGG_struct_inst = new(); // INJECT
        end
        // Initialize dynamic arrays before randomization if needed,
        // but Verilator should handle their randomization if rand
        // GGG_struct_inst.GGG_q = {1, 2, 3}; // Example initialization - Removed
        // GGG_struct_inst.GGG_aa = '{"key1": 10, "key2": 20}; // Example initialization - Removed

        void'(GGG_struct_inst.randomize()); //INJECT

        GGGout = {GGG_struct_inst.GGG_ps.GGG_f1, GGG_struct_inst.GGG_ua[0]}; //INJECT
    end

    //INJECT

endmodule

module GGG_constraint_blocks (
    input bit GGGin,
    output int GGGout
);

    //INJECT

    class GGG_constrained_class; //INJECT
        rand int GGG_val1; //INJECT
        rand int GGG_val_array[5]; //INJECT

        constraint GGG_basic_constr { //INJECT
            GGG_val1 > 5; //INJECT
        }

        constraint GGG_if_constr { //INJECT
            if (GGG_val1 > 10) { //INJECT
                GGG_val_array[0] < 5; //INJECT
            } else { //INJECT
                GGG_val_array[0] > 15; //INJECT
            } //INJECT
        }

        constraint GGG_foreach_constr { //INJECT
            foreach (GGG_val_array[GGG_i]) { //INJECT
                GGG_val_array[GGG_i] < 100; //INJECT
            } //INJECT
        }

        virtual function int randomize();
            // Placeholder //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_constrained_class GGG_constr_inst; //INJECT

    always @(posedge GGGin) begin
        // Instance creation needed for linting simulation flow
         if (GGG_constr_inst == null) begin
            GGG_constr_inst = new(); // INJECT
        end
        void'(GGG_constr_inst.randomize()); //INJECT
        GGGout = GGG_constr_inst.GGG_val1 + GGG_constr_inst.GGG_val_array[1]; //INJECT
    end

    //INJECT

endmodule

module GGG_randcase_statement (
    input bit GGGin,
    output int GGGout
);

    //INJECT

    always @(posedge GGGin) begin //INJECT
        randcase //INJECT
            10: GGGout = 1; //INJECT
            5:  GGGout = 2; //INJECT
            1:  GGGout = 3; //INJECT
        endcase
        //INJECT
    end
    //INJECT

endmodule

module GGG_class_inheritance_rand (
    input bit GGGin,
    output int GGGout
);

    //INJECT

    class GGG_base_class; //INJECT
        rand int GGG_base_var; //INJECT

        virtual function int randomize();
            // Placeholder //INJECT
            return 1; //INJECT
        endfunction
        //INJECT

    endclass

    class GGG_derived_class extends GGG_base_class; //INJECT
        rand int GGG_derived_var; //INJECT

        virtual function int randomize();
            // Placeholder logic, Verilator replaces this //INJECT
            int GGG_success = super.randomize(); //INJECT
            return GGG_success; //INJECT
        endfunction
        //INJECT

    endclass

    GGG_derived_class GGG_derived_inst; //INJECT

    always @(posedge GGGin) begin
         // Instance creation needed for linting simulation flow
         if (GGG_derived_inst == null) begin
            GGG_derived_inst = new(); // INJECT
        end
        void'(GGG_derived_inst.randomize()); //INJECT
        GGGout = GGG_derived_inst.GGG_base_var + GGG_derived_inst.GGG_derived_var; //INJECT
    end

    //INJECT

endmodule
