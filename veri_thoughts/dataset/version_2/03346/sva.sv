module dff_with_set_sva (
    input logic Q,
    input logic D,
    input logic CLK,
    input logic SET,
    input logic NOTIFIER,
    input logic VPWR,
    input logic VGND
);

    // Sampling clock is CLK; SET is an active-low asynchronous clear.
    // Q is sequential; NOTIFIER is continuously driven from Q and D in the RTL.

    // When SET is asserted low, Q must be low.
    check_set_low_clears_q: assert property (
        @(posedge CLK) !SET |-> (Q == 1'b0)
    );

    // In normal operation, NOTIFIER must match the Q/D mismatch function.
    check_notifier_matches_mismatch_active: assert property (
        @(posedge CLK) disable iff (!SET) (NOTIFIER == (Q != D))
    );

    // During clear, NOTIFIER must still match the Q/D mismatch function.
    check_notifier_matches_mismatch_during_clear: assert property (
        @(posedge CLK) !SET |-> (NOTIFIER == (Q != D))
    );

endmodule