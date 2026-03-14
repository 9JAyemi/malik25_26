module top_module_sva (
    input logic a,
    input logic b,
    input logic out_always_comb
);
    // Out equals XOR of inputs.
    check_xor_equivalence: assert property (
        @($global_clock) out_always_comb == (a ^ b)
    );

    // When inputs are equal, output is 0.
    check_equal_inputs_low: assert property (
        @($global_clock) (a == b) |-> (out_always_comb == 1'b0)
    );

    // When inputs differ, output is 1.
    check_diff_inputs_high: assert property (
        @($global_clock) (a != b) |-> (out_always_comb == 1'b1)
    );

    // For a=0,b=0, output is 0.
    check_case_00_low: assert property (
        @($global_clock) (!a && !b) |-> (out_always_comb == 1'b0)
    );

    // For a=1,b=1, output is 0.
    check_case_11_low: assert property (
        @($global_clock) (a && b) |-> (out_always_comb == 1'b0)
    );

    // For a=0,b=1, output is 1.
    check_case_01_high: assert property (
        @($global_clock) (!a && b) |-> (out_always_comb == 1'b1)
    );

    // For a=1,b=0, output is 1.
    check_case_10_high: assert property (
        @($global_clock) (a && !b) |-> (out_always_comb == 1'b1)
    );

    // If exactly one input changes, output changes.
    check_one_input_change_implies_out_change: assert property (
        @($global_clock) $onehot({$changed(a), $changed(b)}) |-> $changed(out_always_comb)
    );

    // If both inputs change together, output remains stable.
    check_both_inputs_change_keeps_out_stable: assert property (
        @($global_clock) ($changed(a) && $changed(b)) |-> $stable(out_always_comb)
    );

    // If output changes, exactly one input must have changed.
    check_out_change_implies_one_input_change: assert property (
        @($global_clock) $changed(out_always_comb) |-> $onehot({$changed(a), $changed(b)})
    );
endmodule