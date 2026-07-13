module sky130_fd_sc_ms__a22o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Combinational a22o: X = (A1 & A2) | (B1 & B2); no clock/reset in RTL, sample on input edges.

    ///// Functional equivalence on each input edge /////
    // X equals (A1&A2)|(B1&B2) when sampled on A1 rising.
    check_func_eq_on_A1: assert property (
        @(posedge A1) X == ((A1 & A2) | (B1 & B2))
    );
    // X equals (A1&A2)|(B1&B2) when sampled on A2 rising.
    check_func_eq_on_A2: assert property (
        @(posedge A2) X == ((A1 & A2) | (B1 & B2))
    );
    // X equals (A1&A2)|(B1&B2) when sampled on B1 rising.
    check_func_eq_on_B1: assert property (
        @(posedge B1) X == ((A1 & A2) | (B1 & B2))
    );
    // X equals (A1&A2)|(B1&B2) when sampled on B2 rising.
    check_func_eq_on_B2: assert property (
        @(posedge B2) X == ((A1 & A2) | (B1 & B2))
    );

    ///// One-way implications derived from the logic /////
    // If A1&A2 is 1, X must be 1 (sampled on A1).
    check_A_and_implies_X_on_A1: assert property (
        @(posedge A1) (A1 & A2) |=> (X == 1'b1)
    );
    // If B1&B2 is 1, X must be 1 (sampled on B1).
    check_B_and_implies_X_on_B1: assert property (
        @(posedge B1) (B1 & B2) |=> (X == 1'b1)
    );
    // If neither A1&A2 nor B1&B2 is 1, X must be 0 (sampled on A2).
    check_neither_and_implies_X0_on_A2: assert property (
        @(posedge A2) (!(A1 & A2) && !(B1 & B2)) |=> (X == 1'b0)
    );
    // If X is 1, at least one of A1&A2 or B1&B2 is 1 (sampled on B2).
    check_X1_implies_one_and_on_B2: assert property (
        @(posedge B2) (X == 1'b1) |=> ((A1 & A2) | (B1 & B2))
    );
    // If X is 0, neither A1&A2 nor B1&B2 is 1 (sampled on A1).
    check_X0_implies_neither_and_on_A1: assert property (
        @(posedge A1) (X == 1'b0) |=> (!(A1 & A2) && !(B1 & B2))
    );

endmodule