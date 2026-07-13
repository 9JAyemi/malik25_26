module pulse_generator_sva (
    input logic D,
    input logic Q,
    input logic pulse
);

    // Clock: Q; reset: none; logic: sequential on posedge Q.

    // From the third sampled clock onward, pulse matches a prior sampled 0->1 on D.
    check_pulse_matches_prior_sampled_rise: assert property (
        @(posedge Q) (##2 1'b1) |-> (pulse == ($past(D) && !$past(D,2)))
    );

    // A prior sampled low-to-high transition on D produces pulse.
    check_prior_low_to_high_generates_pulse: assert property (
        @(posedge Q) (##2 ($past(D) && !$past(D,2))) |-> pulse
    );

    // Consecutive sampled highs on D do not retrigger pulse.
    check_prior_high_to_high_suppresses_pulse: assert property (
        @(posedge Q) (##2 ($past(D) && $past(D,2))) |-> !pulse
    );

    // If D was low on the prior sampled clock, pulse is low now.
    check_prior_low_clears_pulse: assert property (
        @(posedge Q) (##1 (!$past(D))) |-> !pulse
    );

    // pulse can only occur if D was high on the prior sampled clock.
    check_pulse_requires_prior_high_d: assert property (
        @(posedge Q) (##1 pulse) |-> $past(D)
    );

    // Once established, pulse is only one sampled clock wide.
    check_pulse_is_single_cycle: assert property (
        @(posedge Q) (##1 pulse) |-> ##1 !pulse
    );

endmodule