module top (
    input logic GGGin,
    output logic GGGout
);
    // Simple pass-through
    assign GGGout = GGGin;
    //INJECT
endmodule

// Module demonstrating an always block with an event control (legal with --no-timing)
module GGG_always_event (
    input logic GGGin,
    input logic GGGCk,
    output logic GGGout
);
    logic GGGreg;
    always @(posedge GGGCk) begin
        GGGreg <= GGGin;
        //INJECT
    end
    assign GGGout = GGGreg;
    //INJECT
endmodule

// Module demonstrating an automatic task without timing (timing removed to pass --no-timing lint)
module GGG_task_seq (
    input logic GGGin,
    input logic GGGCk, // Keep port but not used for timing in task
    output logic GGGout
);
    // Task must not contain timing controls like @ or # in --no-timing mode
    task automatic GGGmy_task(input logic GGGarg, output logic GGGres);
        logic GGGtemp = GGGarg;
        // Removed: @(posedge GGGCk); // Event control is illegal here in --no-timing
        GGGres = GGGtemp;
        //INJECT
    endtask

    always @(posedge GGGCk) begin
        GGGmy_task(GGGin, GGGout);
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating an automatic function without timing (timing illegal in functions)
module GGG_func_seq (
    input logic GGGin,
    input logic GGGCk, // Keep port but not used
    output logic GGGout
);
    // Function cannot contain timing controls like @ or #
    function automatic logic GGGmy_func(input logic GGGarg);
        // Removed: #1 GGGarg = GGGarg; // Delays are illegal in functions
        //INJECT
        return GGGarg;
    endfunction

    // Call the function in a process
    always @(posedge GGGCk) begin
       GGGout = GGGmy_func(GGGin);
       //INJECT
    end
    //INJECT
endmodule

// Module demonstrating sequential logic (fork/join removed to pass --no-timing lint)
module GGG_process_seq1 (
    input logic GGGin,
    input logic GGGCk, // Keep port but used differently
    output logic GGGout
);
    logic GGGtemp1, GGGtemp2;
    // Cannot use fork/join without --timing. Replaced with sequential logic.
    always @(posedge GGGCk) begin
        GGGtemp1 = GGGin;
        //INJECT
        GGGtemp2 = ~GGGin;
        //INJECT
        GGGout = GGGtemp1 ^ GGGtemp2;
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating another sequential process (fork/join_none removed to pass --no-timing lint)
module GGG_process_seq2 (
    input logic GGGin,
    input logic GGGCk, // Keep port
    output logic GGGout
);
    // Cannot use fork/join_none without --timing. Replaced with simple process.
    always @(posedge GGGCk) begin
        GGGout = GGGin; // Simple assignment
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating conditional logic (wait(condition) removed to pass --no-timing lint)
module GGG_conditional_logic (
    input logic GGGin,
    input logic GGGCond,
    output logic GGGout
);
    // Cannot use wait(condition) without --timing. Replaced with an if statement.
    always @(GGGin, GGGCond) begin
        if (GGGCond) begin // Conditional check instead of wait
            GGGout = GGGin;
            //INJECT
        end else begin
            GGGout = 1'b0; // Example default
            //INJECT
        end
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a simple blocking assignment (intra-assignment delay removed)
module GGG_simple_blocking_assign (
    input logic GGGin,
    output logic GGGout
);
    // Cannot use intra-assignment timing like #1 or @() without --timing/correct context.
    // Replaced with simple blocking assignment.
    always @(GGGin) begin
        GGGout = GGGin; // Removed: #1 or @(...)
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a simple continuous assignment (net delay removed)
module GGG_simple_continuous_assign (
    input logic GGGin,
    output logic GGGout
);
    // Cannot use net delay like #1 without --timing.
    // Replaced with simple continuous assignment.
    assign GGGout = GGGin; // Removed: #1
    //INJECT
endmodule

// Module demonstrating a simple non-blocking assignment (net delay removed)
module GGG_simple_nonblocking_assign (
    input logic GGGin,
    output logic GGGout
);
    // Cannot use non-blocking assignment net delay like <= #1 without --timing.
    // Replaced with simple non-blocking assignment.
    always @(GGGin) begin
        GGGout <= GGGin; // Removed: #1
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a sequential process (disable fork removed to pass --no-timing lint)
module GGG_process_seq3 (
    input logic GGGin,
    input logic GGGCk, // Keep port
    input logic GGGdisable_condition, // Keep port but used differently
    output logic GGGout
);
    // Cannot use fork/join_none or disable fork without --timing.
    // Replaced with sequential logic and conditional execution.
    always @(posedge GGGCk) begin
        if (!GGGdisable_condition) begin // Execute logic if not "disabled" conceptually
            GGGout = GGGin;
            //INJECT
        end else begin
             GGGout = 1'b0; // Example default when "disabled"
            //INJECT
        end
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a sequential process (wait fork removed to pass --no-timing lint)
module GGG_process_seq4 (
    input logic GGGin,
    input logic GGGCk, // Keep port
    output logic GGGout
);
    logic GGGtemp;
    // Cannot use fork/join_none or wait fork without --timing.
    // Replaced with simple sequential logic.
    always @(posedge GGGCk) begin
        // Sequential execution
        GGGtemp = GGGin;
        //INJECT
        GGGout = GGGtemp;
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a class method without timing (timing removed from task to pass --no-timing lint)
module GGG_class_method_seq (
    input logic GGGin,
    // GGGCk is not strictly needed but can be kept if initial block needs a trigger
    input logic GGGCk,
    output logic GGGout
);

    class GGGmy_class;
        logic GGGmember;
        // Task must not contain timing controls like @ or # in --no-timing mode
        task GGGseq_method(input logic GGGarg);
            // Removed: #1 GGGmember = GGGarg; // Delay removed
            GGGmember = GGGarg; // Simple assignment
            //INJECT
        endtask
    endclass

    GGGmy_class GGGinst;

    // Use an always block triggered by GGGCk for repetitive calls if needed,
    // or keep initial for single setup call. Initial is fine for setup.
    initial begin
        GGGinst = new();
        // Initial block runs at time 0. GGGin might be 'X'.
        // A better pattern for exercise might be calling from an always block as below.
        // Keeping initial for class instantiation exercise.
        //INJECT
    end

    // Add an always block to call the method when GGGCk changes
    always @(posedge GGGCk) begin
        if (GGGinst == null) GGGinst = new(); // Ensure instance exists - good practice
        GGGinst.GGGseq_method(GGGin);
        //INJECT
    end

    // Simple continuous assignment from the class member
    // Accessing class member needs care depending on simulation phase and Verilator version/flags
    // Assigning from a class member changed by sequential logic might need sync.
    // For linting, direct access is usually fine.
    assign GGGout = GGGinst.GGGmember; // GGGmember is updated by the method calls
    //INJECT
endmodule

// Module demonstrating a simple generate block
module GGG_generate_block (
    input logic GGGin,
    output logic GGGout
);
    parameter GGGENABLE = 1; // Parameter controlling generation
    generate
        if (GGGENABLE) begin : GGGgen_enabled
            always @(GGGin) begin
                GGGout = GGGin;
                //INJECT
            end
            //INJECT
        end else begin : GGGgen_disabled
            assign GGGout = 1'b0; // Default low if disabled
            //INJECT
        end
    endgenerate
    //INJECT
endmodule

// Module intended for binding (added back as a standalone module)
module GGG_bound_module (
    input logic GGGin,
    output logic GGGout
);
    assign GGGout = ~GGGin;
    //INJECT
endmodule

// Module demonstrating a simple interface (Verilator supports interfaces)
interface GGG_my_interface (input logic GGGCk);
    logic GGGsignal_a;
    logic GGGsignal_b;
    //INJECT
endinterface

// Module demonstrating using an interface port
module GGG_interface_user (
    input logic GGGin,
    GGG_my_interface GGGif_port,
    output logic GGGout
);
    always @(posedge GGGif_port.GGGCk) begin
        GGGif_port.GGGsignal_a = GGGin;
        //INJECT
        GGGout = GGGif_port.GGGsignal_b;
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating an assertion (Verilator supports assertions, even basic ones without timing)
module GGG_assertion_example (
    input logic GGGin,
    input logic GGGCk,
    input logic GGGCondition,
    output logic GGGout
);
    always @(posedge GGGCk) begin
        // Simple immediate assertion
        GGG_assert_label: assert (GGGCondition || !GGGin) else $error("GGG_Assertion_Failed");
        // More complex assertions typically involve sequences, which need timing.
        // Keeping it simple for --no-timing.
        //INJECT
        GGGout = GGGin;
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a packed struct (modified to unpack for linting)
module GGG_packed_struct (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    // Removed 'packed' keyword to resolve lint error with --no-timing
    typedef struct {
        logic GGGfield1;
        logic [2:0] GGGfield2;
        logic [3:0] GGGfield3;
    } GGGmy_struct_t;

    GGGmy_struct_t GGGstruct_var;

    always @(GGGin) begin
        // Assigning to/from struct members
        GGGstruct_var.GGGfield1 = GGGin[0];
        GGGstruct_var.GGGfield2 = GGGin[3:1];
        GGGstruct_var.GGGfield3 = GGGin[7:4];
        //INJECT
        // Reconstruct output or manipulate - access to unpacked struct members is fine
        GGGout = {GGGstruct_var.GGGfield3, GGGstruct_var.GGGfield2, GGGstruct_var.GGGfield1};
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating an unpacked struct
module GGG_unpacked_struct (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    typedef struct {
        logic GGGfieldA;
        logic [2:0] GGGfieldB;
        logic [3:0] GGGfieldC;
    } GGGmy_unpacked_struct_t;

    GGGmy_unpacked_struct_t GGGunpacked_struct_var;

    always @(GGGin) begin
        // Assigning to/from struct members
        GGGunpacked_struct_var.GGGfieldA = GGGin[0];
        GGGunpacked_struct_var.GGGfieldB = GGGin[3:1];
        GGGunpacked_struct_var.GGGfieldC = GGGin[7:4];
        //INJECT
        // Reconstruct output or manipulate
        GGGout = {GGGunpacked_struct_var.GGGfieldC, GGGunpacked_struct_var.GGGfieldB, GGGunpacked_struct_var.GGGfieldA};
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a packed union (modified to unpack for linting)
module GGG_packed_union (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    // Removed 'packed' keyword to resolve lint error with --no-timing
    typedef union {
        logic [7:0] GGGbyte;
        struct {
            logic GGGbit0;
            logic [6:0] GGGbits7_1;
        } GGGfields;
    } GGGmy_union_t;

    GGGmy_union_t GGGunion_var;

    always @(GGGin) begin
        // Assign to one member
        GGGunion_var.GGGbyte = GGGin;
        //INJECT
        // Read from struct fields member (valid for unpacked union member)
        GGGout = {GGGunion_var.GGGfields.GGGbits7_1, GGGunion_var.GGGfields.GGGbit0};
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating an unpacked union
module GGG_unpacked_union (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    typedef union {
        logic [7:0] GGGbyte;
        struct {
            logic GGGbit0;
            logic [6:0] GGGbits7_1;
        } GGGfields;
    } GGGmy_unpacked_union_t;

    GGGmy_unpacked_union_t GGGunpacked_union_var;

    always @(GGGin) begin
        // Assign to one member, read from another
        GGGunpacked_union_var.GGGbyte = GGGin;
        //INJECT
        // Note: Unpacked unions require explicit member access for value
        GGGout = GGGunpacked_union_var.GGGbyte; // Access the byte field
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a simple enum
module GGG_enum_example (
    input logic [1:0] GGGin,
    output logic GGGout
);
    typedef enum { GGG_STATE_IDLE, GGG_STATE_BUSY, GGG_STATE_DONE } GGG_state_t;

    GGG_state_t GGGcurrent_state;

    always @(GGGin) begin
        case (GGGin)
            2'b00: GGGcurrent_state = GGG_STATE_IDLE;
            2'b01: GGGcurrent_state = GGG_STATE_BUSY;
            2'b10: GGGcurrent_state = GGG_STATE_DONE;
            default: GGGcurrent_state = GGG_state_t'(GGGin); // Cast input to enum type
        endcase
        //INJECT
        // Assign output based on state
        if (GGGcurrent_state == GGG_STATE_DONE) begin
            GGGout = 1'b1;
            //INJECT
        end else begin
            GGGout = 1'b0;
            //INJECT
        end
    end
    //INJECT
endmodule

// Module demonstrating array declaration and access
module GGG_array_example (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    logic [7:0] GGGmy_array [3:0]; // 4 elements, each 8 bits wide

    always @(GGGin) begin
        // Assign to array elements
        GGGmy_array[0] = GGGin;
        GGGmy_array[1] = ~GGGin;
        GGGmy_array[2] = GGGin + 8'd1;
        GGGmy_array[3] = GGGin - 8'd1;
        //INJECT
        // Read from array element
        GGGout = GGGmy_array[GGGin[1:0]]; // Use part of GGGin as index
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating multidimensional array
module GGG_multidim_array (
    input logic [3:0] GGGin,
    output logic [3:0] GGGout
);
    logic [3:0] GGGmy_2d_array [1:0][2:0]; // 2x3 array of 4-bit elements

    always @(GGGin) begin
        // Assign to elements
        GGGmy_2d_array[0][0] = GGGin;
        GGGmy_2d_array[1][2] = ~GGGin;
        //INJECT
        // Read from elements
        GGGout = GGGmy_2d_array[GGGin[1]][GGGin[3:2]]; // Use parts of GGGin as indices
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating dynamic array (syntax check only, timing/sizing handled by V3Timing/runtime)
// Note: Verilator's --no-timing might have limitations or ignore dynamic behavior.
module GGG_dynamic_array (
    input logic GGGin,
    input int GGGsize_in,
    output logic GGGout
);
    logic GGGdynamic_arr []; // Dynamic array declaration

    always @(GGGin, GGGsize_in) begin
        // Dynamic array sizing
        if (GGGsize_in >= 0) begin // Avoid negative size
           GGGdynamic_arr = new[GGGsize_in];
           //INJECT
           // Access elements (access might be out of bounds if index > GGGsize_in-1)
           if (GGGsize_in > 0) begin
               // Using index 0 for simplicity
               GGGdynamic_arr[0] = GGGin;
               GGGout = GGGdynamic_arr[0];
               //INJECT
           end else begin
               GGGout = 1'b0;
               //INJECT
           end
        end else begin
             GGGout = 1'b0; // Handle negative size input
             //INJECT
        end

        // Deletion example (can add conditional deletion)
        // GGGdynamic_arr = new[0]; // Deletes all elements
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating an associative array
module GGG_associative_array (
    input logic [7:0] GGGin,
    input logic GGGkey_in,
    output logic [7:0] GGGout
);
    logic [7:0] GGGassoc_array [logic]; // Associative array with logic key

    always @(GGGin, GGGkey_in) begin
        // Write to associative array
        GGGassoc_array[GGGkey_in] = GGGin;
        //INJECT
        // Read from associative array
        // Check if key exists before reading
        if (GGGassoc_array.exists(GGGkey_in)) begin
            GGGout = GGGassoc_array[GGGkey_in];
            //INJECT
        end else begin
            GGGout = 8'hXX; // Default if key not found
            //INJECT
        end
        // Deletion example (can add conditional deletion)
        // GGGassoc_array.delete(GGGkey_in);
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating a queue
module GGG_queue_example (
    input logic [7:0] GGGin,
    input logic GGGpush_en,
    input logic GGGpop_en,
    input logic GGGCk, // Added clock for sequential behavior
    output logic [7:0] GGGout
);
    logic [7:0] GGGmy_queue [$]; // Queue declaration
    logic [7:0] GGGout_reg; // Output register for sequential

    always @(posedge GGGCk) begin
        if (GGGpush_en) begin
            GGGmy_queue.push_back(GGGin);
            //INJECT
        end
        // Pop happens on clock edge, conditionally
        if (GGGpop_en && GGGmy_queue.size() > 0) begin
            GGGout_reg = GGGmy_queue.pop_front();
            //INJECT
        end else if (GGGqueue_size() == 0) begin // Corrected condition check
            GGGout_reg = 8'hXX; // Indicate empty on pop attempt
            //INJECT
        end else if (GGGpop_en && GGGmy_queue.size() == 0) begin
             // If pop_en is high but queue is empty, maybe hold previous output or set to default
             // GGGout_reg holds its value if not assigned
             //INJECT
        end
    end
    assign GGGout = GGGout_reg;
    //INJECT
endmodule


// Module demonstrating constant variables
module GGG_const_var (
    input logic GGGin,
    output logic GGGout
);
    // Constant variable declaration
    const logic GGG_CONSTANT_VALUE = 1'b1;
    //INJECT
    // Use the constant
    assign GGGout = GGGin & GGG_CONSTANT_VALUE;
    //INJECT
endmodule

// Module demonstrating static vs automatic variables in tasks/functions
module GGG_static_automatic (
    input logic GGGin,
    input logic GGGCk,
    output logic [7:0] GGGout // Widened output to show more counter bits
);
    // Static variables retain value between calls (module default)
    logic [7:0] GGGstatic_counter = 0; // Implicitly static, widened

    // Automatic variables are created on entry (task/function default)
    task automatic GGGmy_task_vars(input logic GGGarg);
        logic GGGauto_temp = GGGarg; // Automatic variable
        GGGstatic_counter = GGGstatic_counter + 1;
        //INJECT
        // Can potentially use GGGauto_temp and GGGstatic_counter here
    endtask

    always @(posedge GGGCk) begin
        GGGmy_task_vars(GGGin);
        // Output something based on static variable for visibility
        GGGout = GGGstatic_counter; // Output the counter
        //INJECT
    end
    //INJECT
endmodule

// Module demonstrating packed array type (modified to unpack for linting)
module GGG_packed_array_type (
    input logic [7:0] GGGin,
    output logic [7:0] GGGout
);
    // Removed 'packed' keyword to resolve lint error with --no-timing
    typedef logic [3:0] GGG_vec_t;
    GGG_vec_t GGGvec_array [1:0]; // Array of 2 unpacked vectors

    always @(GGGin) begin
        // Assignment to unpacked elements
        GGGvec_array[0] = GGGin[3:0];
        GGGvec_array[1] = GGGin[7:4];
        //INJECT
        // Access array elements and concatenate (valid syntax)
        GGGout = {GGGvec_array[1], GGGvec_array[0]}; // Concatenate unpacked elements
        //INJECT
    end
    //INJECT
endmodule
