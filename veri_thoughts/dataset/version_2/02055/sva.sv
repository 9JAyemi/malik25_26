module top_module_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_func
);
    // out_func equals OR of the two XOR results of (a,b) and (c,d)
    check_function_equivalence_xor_or: assert property (
        @(posedge CLK) out_func == ((a ^ b) || (c ^ d))
    );

    // out_func equals (a!=b)||(c!=d)
    check_function_equivalence_neq_or: assert property (
        @(posedge CLK) out_func == ((a != b) || (c != d))
    );

    // When both pairs are equal, out_func must be 0
    check_zero_when_both_pairs_equal: assert property (
        @(posedge CLK) ((a == b) && (c == d)) |-> (out_func == 1'b0)
    );

    // If a and b differ, out_func must be 1
    check_one_when_ab_differs: assert property (
        @(posedge CLK) (a != b) |-> (out_func == 1'b1)
    );

    // If c and d differ, out_func must be 1
    check_one_when_cd_differs: assert property (
        @(posedge CLK) (c != d) |-> (out_func == 1'b1)
    );

    // If out_func is 0, both pairs must be equal
    check_zero_implies_both_pairs_equal: assert property (
        @(posedge CLK) (out_func == 1'b0) |-> ((a == b) && (c == d))
    );

    // If out_func is 1, at least one pair must differ
    check_one_implies_some_pair_differs: assert property (
        @(posedge CLK) (out_func == 1'b1) |-> ((a != b) || (c != d))
    );

    // If inputs are stable across a cycle, out_func must be stable
    check_stable_out_when_inputs_stable: assert property (
        @(posedge CLK) (!$changed(a) && !$changed(b) && !$changed(c) && !$changed(d)) |-> (!$changed(out_func))
    );

    // If out_func changes, at least one input must have changed
    check_out_change_requires_input_change: assert property (
        @(posedge CLK) $changed(out_func) |-> ($changed(a) || $changed(b) || $changed(c) || $changed(d))
    );
endmodule