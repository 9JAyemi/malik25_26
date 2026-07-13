module top_module_sva (
    input logic a,
    input logic b,
    input logic out_wire
);
    // On posedge of a, out must equal ~b (since a==1).
    check_out_eq_notb_on_posedge_a: assert property (
        @(posedge a) (out_wire == ~b)
    );

    // On negedge of a, out must equal b (since a==0).
    check_out_eq_b_on_negedge_a: assert property (
        @(negedge a) (out_wire == b)
    );

    // On posedge of b, out must equal ~a (since b==1).
    check_out_eq_nota_on_posedge_b: assert property (
        @(posedge b) (out_wire == ~a)
    );

    // On negedge of b, out must equal a (since b==0).
    check_out_eq_a_on_negedge_b: assert property (
        @(negedge b) (out_wire == a)
    );

    // Out rising implies inputs differ (out==1).
    check_inputs_diff_on_posedge_out: assert property (
        @(posedge out_wire) (a != b)
    );

    // Out falling implies inputs equal (out==0).
    check_inputs_equal_on_negedge_out: assert property (
        @(negedge out_wire) (a == b)
    );

    // On any input edge, out must equal a ^ b.
    check_xor_on_input_edges: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (out_wire == (a ^ b))
    );

    // On any out edge, out must equal a ^ b.
    check_xor_on_output_edges: assert property (
        @(posedge out_wire or negedge out_wire) (out_wire == (a ^ b))
    );
endmodule