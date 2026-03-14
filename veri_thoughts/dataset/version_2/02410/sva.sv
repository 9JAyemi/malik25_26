module sky130_fd_sc_hd__a32o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // No clock or reset in RTL; pure combinational; sample on any input edge.

    // X equals (A1 & A2 & A3) | (B1 & B2).
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        X == ((A1 & A2 & A3) | (B1 & B2))
    );

    // If A1&A2&A3 are all HIGH, X must be HIGH.
    check_A_term_implies_X: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (A1 & A2 & A3) |-> (X == 1'b1)
    );

    // If B1&B2 are both HIGH, X must be HIGH.
    check_B_term_implies_X: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (B1 & B2) |-> (X == 1'b1)
    );

    // If X is HIGH, at least one AND-term is HIGH.
    check_X_high_has_minterm: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (X == 1'b1) |-> ((A1 & A2 & A3) || (B1 & B2))
    );

    // If both AND-terms are LOW, X must be LOW.
    check_no_minterm_implies_X_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (!((A1 & A2 & A3)) && !(B1 & B2)) |-> (X == 1'b0)
    );

    // When A-term is LOW, X reduces to B1&B2.
    check_reduce_when_A_term_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (!(A1 & A2 & A3)) |-> (X == (B1 & B2))
    );

    // When B-term is LOW, X reduces to A1&A2&A3.
    check_reduce_when_B_term_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        (!(B1 & B2)) |-> (X == (A1 & A2 & A3))
    );

    // If all inputs are LOW, X must be LOW.
    check_all_zero_implies_X_zero: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0) && (B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // If A1,A2,A3 and B1,B2 are all HIGH, X must be HIGH.
    check_all_one_implies_X_one: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge A3 or negedge A3 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2)
        ((A1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1)) |-> (X == 1'b1)
    );

endmodule