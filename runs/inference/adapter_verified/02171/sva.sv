module sky130_fd_sc_ls__a222o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);

// X matches the implemented 3-input OR of the three AND terms.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2) | (C1 & C2))
    );

// A1 and A2 high together force X high.
    check_a_pair_forces_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

// B1 and B2 high together force X high.
    check_b_pair_forces_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

// C1 and C2 high together force X high.
    check_c_pair_forces_x_high: assert property (
        @(posedge clk) (C1 & C2) |-> X
    );

// With no pair of inputs high together, X must be low.
    check_no_pair_means_x_low: assert property (
        @(posedge clk) !(A1 & A2 & B1 & B2 & C1 & C2) |-> !X
    );

// X high implies at least one input pair is high together.
    check_x_high_implies_pair_high: assert property (
        @(posedge clk) X |-> (A1 & A2) || (B1 & B2) || (C1 & C2)
    );

endmodule
