module d_flip_flop_sva (
    input logic D,
    input logic CLK,
    input logic RESET,
    input logic SET,
    input logic Q
);

    // Active-low reset clears Q by the next sampled clock.
    check_reset_clears_q: assert property (
        @(posedge CLK) !RESET |=> (Q == 1'b0)
    );

    // With reset inactive and SET low, D=0 is captured into Q.
    check_capture_zero_when_set_low: assert property (
        @(posedge CLK) disable iff (!RESET) (!SET && !D) |=> (Q == 1'b0)
    );

    // A high Q must come from a prior SET or a prior D=1 when reset was inactive.
    check_q_high_has_valid_source: assert property (
        @(posedge CLK) disable iff (!RESET)
        (!$initstate && Q) |-> ($past(RESET) && ($past(SET) || $past(D)))
    );

    // If prior D was 0, a high Q must have been caused by SET.
    check_q_high_with_d_zero_requires_set: assert property (
        @(posedge CLK) disable iff (!RESET)
        (!$initstate && Q && !$past(D)) |-> ($past(RESET) && $past(SET))
    );

    // If prior SET was 0, a high Q must have come from D=1.
    check_q_high_with_set_low_requires_d: assert property (
        @(posedge CLK) disable iff (!RESET)
        (!$initstate && Q && !$past(SET)) |-> ($past(RESET) && $past(D))
    );

endmodule