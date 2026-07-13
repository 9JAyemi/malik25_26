module ODDR_sva (
    input logic D1,
    input logic D2,
    input logic C,
    input logic CE,
    input logic R,
    input logic Q
);

    // Clock is posedge C; this RTL has no reset.
    // With CE high and R low, Q loads D1.
    check_capture_d1: assert property (
        @(posedge C) disable iff (1'b0)
        (CE === 1'b1 && R === 1'b0) |=> (Q === $past(D1))
    );

    // With CE high and R not low, Q loads D2.
    check_capture_d2: assert property (
        @(posedge C) disable iff (1'b0)
        (CE === 1'b1 && R !== 1'b0) |=> (Q === $past(D2))
    );

    // With CE not high, Q holds its previous value.
    check_hold_when_ce_not_high: assert property (
        @(posedge C) disable iff (1'b0)
        (CE !== 1'b1) |=> (Q === $past(Q))
    );

endmodule