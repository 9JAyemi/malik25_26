module counter_4bit_sync_reset_sva (
    input logic CK,
    input logic RST,
    input logic [3:0] Q
);

// Clock: CK (posedge). Reset: RST synchronous active-high. Logic: sequential 4-bit counter.

    // When RST is HIGH at a clock edge, Q must be 0 on the next clock.
    reset_clears_next: assert property (
        @(posedge CK) RST |=> (Q == 4'b0000)
    );

// If RST is HIGH in consecutive cycles, Q must be 0 in the current cycle.
    reset_holds_zero: assert property (
        @(posedge CK) RST && $past(RST) |-> (Q == 4'b0000)
    );

// If RST is LOW and Q is 0 at a clock edge, it must have been 0 on the previous cycle.
    zero_preserved_when_not_reset: assert property (
        @(posedge CK) disable iff (RST) (Q == 4'b0000) |-> $past(Q == 4'b0000)
    );

// If RST is LOW and Q is not 0 at a clock edge, it must have been non-zero on the previous cycle.
    nonzero_preserved_when_not_reset: assert property (
        @(posedge CK) disable iff (RST) (Q != 4'b0000) |-> $past(Q != 4'b0000)
    );

// When not in reset, Q increments by 1 modulo 16 each cycle.
    count_increments_mod16: assert property (
        @(posedge CK) disable iff (RST) 1'b1 |=> (Q == ($past(Q) + 4'd1))
    );

// When not in reset, Q never holds its previous value.
    count_never_holds: assert property (
        @(posedge CK) disable iff (RST) 1'b1 |=> (Q != $past(Q))
    );

// When not in reset, Q wraps from 15 back to 0.
    count_wraps_from_max: assert property (
        @(posedge CK) disable iff (RST) (Q == 4'hF) |=> (Q == 4'h0)
    );

endmodule
