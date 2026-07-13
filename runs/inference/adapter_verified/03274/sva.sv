module dffr_sva (
    input logic Q,
    input logic D,
    input logic C,
    input logic R
);

// Clock: C (posedge). Reset: R (active-low, asynchronous). Sequential DFF with reset.

    // When reset is asserted low at a clock edge, Q must be 0 on the next clock.
    reset_clears_next: assert property (
        @(posedge C) !R |=> (Q == 1'b0)
    );

// If reset is low in consecutive cycles, Q is 0 in the later cycle.
    reset_holds_zero: assert property (
        @(posedge C) (!R && $past(!R)) |=> (Q == 1'b0)
    );

// With reset high, Q captures D on the next clock.
    capture_d_when_reset_high: assert property (
        @(posedge C) disable iff (!R) 1'b1 |=> (Q == $past(D))
    );

// With reset high, Q holds its value when D equals current Q.
    hold_when_d_equals_q: assert property (
        @(posedge C) disable iff (!R) (D == Q) |=> (Q == $past(Q))
    );

// With reset high, Q changes to D when D differs from current Q.
    change_when_d_differs: assert property (
        @(posedge C) disable iff (!R) (D != Q) |=> (Q == $past(D))
    );

endmodule
