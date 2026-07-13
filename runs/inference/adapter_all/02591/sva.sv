module magnitude_comparator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       out
);

    // out must match the RTL's magnitude comparison.
    check_out_matches_magnitude_compare: assert property (
        @($global_clock) out == (|A > |B)
    );

    // A greater magnitude must drive out high.
    check_a_greater_sets_out: assert property (
        @($global_clock) (|A > |B) |-> out
    );

    // A equal to B must drive out low.
    check_a_equal_b_clears_out: assert property (
        @($global_clock) (|A == |B) |-> !out
    );

    // B greater magnitude must drive out low.
    check_b_greater_clears_out: assert property (
        @($global_clock) (|A < |B) |-> !out
    );

    // Stable inputs must keep the combinational output stable.
    check_stable_inputs_keep_out_stable: assert property (
        @($global_clock) ($stable(A) && $stable(B)) |-> $stable(out)
    );

endmodule