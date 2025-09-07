module keyword_var_and_func_vars (
    input logic         in_data,
    output logic [7:0]  out_sum
);
    logic module_keyword_like_var;
    logic [7:0] temp_val;
    always_comb begin
        module_keyword_like_var = in_data;
        temp_val = 8'h00;
        if (module_keyword_like_var) begin
            temp_val = 8'hFF;
        end
        out_sum = temp_val;
    end
    function automatic [7:0] calculate_offset(input [3:0] val);
        logic [7:0] func_local_var; 
        func_local_var = val + 4;
        return func_local_var;
    endfunction
    always_comb begin
        out_sum = out_sum + calculate_offset(in_data ? 4'hA : 4'h5);
    end
endmodule
module instantiated_sub_module (
    input wire sub_in,
    output wire sub_out
);
    assign sub_out = sub_in;
endmodule
module module_instantiation_and_public_sig (
    input wire top_in,
    output wire (* public *) top_public_out, 
    output wire top_non_public_out
);
    wire internal_wire; 
    wire sub_result;
    instantiated_sub_module u_sub_mod (
        .sub_in (top_in),
        .sub_out(sub_result)
    );
    assign top_public_out = sub_result;
    assign top_non_public_out = !sub_result;
    assign internal_wire = top_in & sub_result; 
endmodule
module struct_union_and_member_access (
    input logic [15:0] in_data,
    output logic [7:0] out_field_sum
);
    typedef packed struct {
        logic [3:0] field_a; 
        logic [3:0] field_b; 
        logic [7:0] field_c; 
    } my_packed_struct_t;
    typedef packed union {
        logic [15:0] all_data;
        my_packed_struct_t as_struct;
    } my_packed_union_t;
    my_packed_struct_t s_var;
    my_packed_union_t u_var;
    my_packed_struct_t s_var_copy_for_struct_sel; 
    always_comb begin
        s_var.field_a = in_data[3:0]; 
        s_var.field_b = in_data[7:4]; 
        s_var.field_c = in_data[15:8]; 
        u_var.all_data = in_data + 1; 
        u_var.as_struct.field_a = in_data[3:0]; 
        s_var_copy_for_struct_sel = s_var;
        out_field_sum = s_var.field_a + s_var.field_b + u_var.as_struct.field_a + s_var_copy_for_struct_sel.field_c[0];
    end
endmodule
import "DPI-C" function int dpi_add_one(input int value);
module dpi_c_and_scopes_and_class (
    input int in_val,
    output int out_val
);
    int intermediate_dpi_result; 
    int combined_scope_val;
    genvar i;
    generate
        if (in_val[0]) begin : gen_if_block
            assign combined_scope_val = 10;
        end else begin
            assign combined_scope_val = 20;
        end
        for (i=0; i<2; i=i+1) begin : gen_for_block
            logic loop_index_var; 
            assign loop_index_var = in_val[i];
            combined_scope_val = combined_scope_val + (loop_index_var ? 1 : 0);
        end
    endgenerate
    task automatic update_task(input int in_data_task, output int out_data_task);
        int task_local_var; 
        task_local_var = in_data_task + 5;
        out_data_task = task_local_var;
    endtask
    class MySimpleClass;
        logic [7:0] m_data;
        function new(logic [7:0] init_val); 
            m_data = init_val;
        endfunction
        function logic [7:0] get_data(); 
            return m_data;
        endfunction
    endclass
    MySimpleClass my_class_h = null; 
    logic [7:0] class_data_output;
    int task_output;
    always_comb begin
        intermediate_dpi_result = dpi_add_one(in_val);
        update_task(intermediate_dpi_result, task_output);
        if (my_class_h == null) begin
            my_class_h = new(8'hCD);
        end
        class_data_output = my_class_h.get_data(); 
        out_val = intermediate_dpi_result + task_output + combined_scope_val + class_data_output;
    end
endmodule
module level_two_sub (
    input logic [7:0] sub_in_val,
    output logic [7:0] sub_out_val
);
    assign sub_out_val = sub_in_val + 1;
endmodule
module level_one_sub (
    input logic [7:0] mid_in_val,
    output logic [7:0] mid_out_val
);
    typedef struct {
        logic [3:0] part_a;
        logic [3:0] part_b;
    } split_t;
    split_t my_split_struct;
    logic [7:0] level_two_res;
    level_two_sub u_level2_inst (
        .sub_in_val(mid_in_val),
        .sub_out_val(level_two_res)
    );
    always_comb begin
        my_split_struct.part_a = level_two_res[3:0]; 
        my_split_struct.part_b = level_two_res[7:4]; 
        mid_out_val = {my_split_struct.part_b, my_split_struct.part_a};
    end
endmodule
module nested_hierarchy_and_struct_sel (
    input logic [7:0] in_root,
    output logic [7:0] out_root_sum
);
    logic [7:0] level_one_res;
    level_one_sub u_level1_inst (
        .mid_in_val(in_root),
        .mid_out_val(level_one_res)
    );
    assign out_root_sum = level_one_res + in_root;
endmodule
