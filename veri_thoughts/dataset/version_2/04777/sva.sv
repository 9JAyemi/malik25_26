module xor_pipeline_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out
);

    // out equals the XOR of the two previous sampled input parities.
    check_out_matches_prior_sampled_parities: assert property (
        @(posedge clk)
        $past(1'b1, 2) |-> (out == (($past(a, 2) ^ $past(b, 2)) ^ ($past(a) ^ $past(b))))
    );

    // Unchanged input parity produces a low out on the next cycle.
    check_out_low_when_parity_is_stable: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a ^ b) == (a ^ b))) |=> (out == 1'b0)
    );

    // Changed input parity produces a high out on the next cycle.
    check_out_high_when_parity_changes: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a ^ b) != (a ^ b))) |=> (out == 1'b1)
    );

    // Unchanged inputs keep parity stable and force out low on the next cycle.
    check_out_low_when_inputs_hold: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a) == a) && ($past(b) == b)) |=> (out == 1'b0)
    );

    // Toggling both inputs together keeps parity stable and forces out low.
    check_out_low_when_both_inputs_toggle: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a) != a) && ($past(b) != b)) |=> (out == 1'b0)
    );

    // Toggling only a changes parity and forces out high on the next cycle.
    check_out_high_when_only_a_toggles: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a) != a) && ($past(b) == b)) |=> (out == 1'b1)
    );

    // Toggling only b changes parity and forces out high on the next cycle.
    check_out_high_when_only_b_toggles: assert property (
        @(posedge clk)
        ($past(1'b1) && ($past(a) == a) && ($past(b) != b)) |=> (out == 1'b1)
    );

endmodule