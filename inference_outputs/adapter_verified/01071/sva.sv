module sky130_fd_sc_ms__a211o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// X matches the implemented A211O function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

// B1 high forces X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

// C1 high forces X high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

// A1 and A2 high together force X high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

// With no asserted OR term, X must be low.
    check_no_or_term_means_x_low: assert property (
        @(posedge clk) !(B1 | C1 | (A1 & A2)) |-> !X
    );

// X low implies no asserted OR term.
    check_x_low_implies_no_or_term: assert property (
        @(posedge clk) !X |-> !(B1 | C1 | (A1 & A2))
    );

endmodule
