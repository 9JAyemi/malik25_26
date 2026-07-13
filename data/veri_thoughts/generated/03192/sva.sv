module my_or2_sva (
    input logic A,
    input logic B,
    input logic X,
    input logic PG
);

    // No clock or reset in RTL; this is purely combinational.
    // X must always equal the OR of A and B.
    check_x_matches_or: assert property (
        @($global_clock) X == (A | B)
    );

    // PG must always be tied high.
    check_pg_tied_high: assert property (
        @($global_clock) PG == 1'b1
    );

endmodule