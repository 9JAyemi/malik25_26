module sky130_fd_sc_hvl__a22o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

// X must equal the OR of the two AND terms.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | (B1 & B2))
    );

// A high A pair must drive X high.
    check_a_pair_forces_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

// A high B pair must drive X high.
    check_b_pair_forces_x_high: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

// With no asserted input pair, X must be low.
    check_no_pair_means_x_low: assert property (
        @(posedge clk) !(A1 & A2 & B1 & B2) |-> !X
    );

// A high X must come from at least one input pair.
    check_x_high_has_a_pair: assert property (
        @(posedge clk) X |-> (A1 & A2) || (B1 & B2)
    );

endmodule
