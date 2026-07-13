module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

// X must equal the OR of the two 3-input AND terms.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2 & A3) | (B1 & B2))
    );

// All three A inputs high must drive X high.
    check_a_triplet_sets_x: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

// Both B inputs high must drive X high.
    check_b_pair_sets_x: assert property (
        @(posedge clk) (B1 & B2) |-> X
    );

// X low implies neither AND term is satisfied.
    check_x_low_implies_no_term: assert property (
        @(posedge clk) !X |-> (!(A1 & A2 & A3) && !(B1 & B2))
    );

// A high X must come from at least one AND term.
    check_x_high_implies_some_term: assert property (
        @(posedge clk) X |-> (A1 & A2 & A3) || (B1 & B2)
    );

endmodule
