module sky130_fd_sc_lp__a2111o_2_sva (
    input  logic clk,   // sampling clock for assertions (DUT has no clock/reset)
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1,
    input  logic C1,
    input  logic D1
);

    // X equals (A1 & A2) | (B1 & C1 & D1).
    func_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) X == ((A1 & A2) | (B1 & C1 & D1))
    );

    // If A1&A2 is true, X must be 1.
    a_term_implies_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (A1 & A2) |-> (X == 1'b1)
    );

    // If B1&C1&D1 is true, X must be 1.
    bcd_term_implies_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (B1 & C1 & D1) |-> (X == 1'b1)
    );

    // If X is 1, at least one product term is true.
    x_high_implies_some_term_true: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b1) |-> ((A1 & A2) | (B1 & C1 & D1))
    );

    // If both product terms are false, X is 0.
    both_terms_false_implies_x_low: assert property (
        @(posedge clk) disable iff (1'b0) (!(A1 & A2) && !(B1 & C1 & D1)) |-> (X == 1'b0)
    );

    // If X is 0, both product terms must be false.
    x_low_implies_both_terms_false: assert property (
        @(posedge clk) disable iff (1'b0) (X == 1'b0) |-> (!(A1 & A2) && !(B1 & C1 & D1))
    );

    // If B1 is 0, X equals A1&A2.
    b1_zero_selects_and1: assert property (
        @(posedge clk) disable iff (1'b0) (!B1) |-> (X == (A1 & A2))
    );

    // If C1 is 0, X equals A1&A2.
    c1_zero_selects_and1: assert property (
        @(posedge clk) disable iff (1'b0) (!C1) |-> (X == (A1 & A2))
    );

    // If D1 is 0, X equals A1&A2.
    d1_zero_selects_and1: assert property (
        @(posedge clk) disable iff (1'b0) (!D1) |-> (X == (A1 & A2))
    );

    // If A1 is 0, X equals B1&C1&D1.
    a1_zero_selects_and2: assert property (
        @(posedge clk) disable iff (1'b0) (!A1) |-> (X == (B1 & C1 & D1))
    );

    // If A2 is 0, X equals B1&C1&D1.
    a2_zero_selects_and2: assert property (
        @(posedge clk) disable iff (1'b0) (!A2) |-> (X == (B1 & C1 & D1))
    );

    // If all inputs are stable, X must be stable.
    x_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable({A1,A2,B1,C1,D1}) |-> $stable(X)
    );

endmodule