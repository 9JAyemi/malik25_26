module top_module_sva (
    input logic a,
    input logic b,
    input logic out,
    input logic [1:0] internal_out
);
    // Top-level out equals a|b on any input edge.
    check_top_out_is_or_any_edge: assert property (
        @(posedge a or negedge a or posedge b or negedge b) out == (a | b)
    );

    // Internal bit0 equals a|b on any input edge.
    check_internal_out0_is_or_any_edge: assert property (
        @(posedge a or negedge a or posedge b or negedge b) internal_out[0] == (a | b)
    );

    // Top-level out matches internal_out[0] on any input edge.
    check_out_matches_internal0_any_edge: assert property (
        @(posedge a or negedge a or posedge b or negedge b) out == internal_out[0]
    );

    // If both inputs are 0, top-level out must be 0.
    check_out_zero_when_both_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (!a && !b) |-> (out == 1'b0)
    );

    // If a is 1, top-level out must be 1.
    check_out_one_when_a_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) a |-> (out == 1'b1)
    );

    // If b is 1, top-level out must be 1.
    check_out_one_when_b_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) b |-> (out == 1'b1)
    );

    // If top-level out is 0, both inputs must be 0.
    check_inputs_zero_when_out_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (out == 1'b0) |-> (!a && !b)
    );

    // If top-level out is 1, at least one input must be 1.
    check_either_input_one_when_out_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (out == 1'b1) |-> (a || b)
    );

    // If internal_out[0] is 0, both inputs must be 0.
    check_inputs_zero_when_internal0_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (internal_out[0] == 1'b0) |-> (!a && !b)
    );

    // If internal_out[0] is 1, at least one input must be 1.
    check_either_input_one_when_internal0_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (internal_out[0] == 1'b1) |-> (a || b)
    );
endmodule