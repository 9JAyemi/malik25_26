module d_to_t_ff_assertions (
    input logic clk,
    input logic d,
    input logic q
);

    // q matches the two-cycle relation created by the nonblocking assignments.
    check_q_transition_equation: assert property (
        @(posedge clk)
        ($past(1'b1, 2) === 1'b1) |-> (q == ($past(q, 1) & ($past(d, 2) ^ $past(q, 2))))
    );

    // Once q is low, the AND-based update keeps it low on the next cycle.
    check_q_sticky_low: assert property (
        @(posedge clk)
        !q |=> !q
    );

    // A high q requires q to have been high on the previous cycle.
    check_q_high_requires_previous_high: assert property (
        @(posedge clk)
        (($past(1'b1, 1) === 1'b1) && q) |-> $past(q, 1)
    );

    // A high q requires the earlier d^q term to have been high.
    check_q_high_requires_prior_xor_true: assert property (
        @(posedge clk)
        (($past(1'b1, 2) === 1'b1) && q) |-> ($past(d, 2) ^ $past(q, 2))
    );

    // q must clear when prior q was high and the earlier XOR term was low.
    check_q_clears_when_prior_xor_false: assert property (
        @(posedge clk)
        (($past(1'b1, 2) === 1'b1) && $past(q, 1) && ($past(d, 2) == $past(q, 2))) |-> !q
    );

    // q stays high when prior q was high and the earlier XOR term was high.
    check_q_stays_high_when_prior_xor_true: assert property (
        @(posedge clk)
        (($past(1'b1, 2) === 1'b1) && $past(q, 1) && ($past(d, 2) != $past(q, 2))) |-> q
    );

endmodule