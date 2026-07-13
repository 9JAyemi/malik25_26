module DFF_AR_sva (
    input logic CLK,
    input logic RST,
    input logic D,
    input logic Q,
    input logic QN
);

    // Active-low reset forces Q low and QN high.
    check_reset_state: assert property (
        @(posedge CLK) !RST |-> (Q == 1'b0 && QN == 1'b1)
    );

    // Reset has priority over D changes while reset is asserted.
    check_reset_priority_over_d: assert property (
        @(posedge CLK) (!RST && $changed(D)) |-> (Q == 1'b0 && QN == 1'b1)
    );

    // With reset high, Q captures D on the next clock.
    check_q_captures_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (Q == $past(D))
    );

    // With reset high, QN captures the inverse of D on the next clock.
    check_qn_captures_inv_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (QN == ~$past(D))
    );

    // With reset high, Q and QN remain complementary on the next clock.
    check_outputs_complementary: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (QN == ~Q)
    );

endmodule