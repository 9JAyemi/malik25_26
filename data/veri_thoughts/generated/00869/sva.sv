module dffr_sva (
    input logic C,
    input logic R,
    input logic D,
    input logic Q
);
    // Clock: C (posedge). Async reset: R (active-high). Q<=0 on posedge R; else Q<=D on posedge C when !R.

    // Async reset drives Q low immediately on R rising edge.
    check_async_reset_immediate_to_zero: assert property (
        @(posedge R) (Q == 1'b0)
    );

    // On C edge, if reset is high, Q must be 0 (reset dominates).
    check_reset_dominates_clocked_update: assert property (
        @(posedge C) R |-> (Q == 1'b0)
    );

    // While reset is held across consecutive C edges, Q remains 0 and stable.
    check_zero_stable_during_held_reset: assert property (
        @(posedge C) (R && $past(R)) |-> ((Q == 1'b0) && ($past(Q) == 1'b0))
    );

    // On the first C edge after reset deasserts, Q is still 0 before capturing new D.
    check_q_zero_on_cycle_after_reset_release: assert property (
        @(posedge C) disable iff (R) ($past(R) && !R) |-> (Q == 1'b0)
    );

    // Q can be high only when not in reset.
    check_q_one_only_when_not_in_reset: assert property (
        @(posedge C) disable iff (R) (Q == 1'b1) |-> (!R)
    );
endmodule