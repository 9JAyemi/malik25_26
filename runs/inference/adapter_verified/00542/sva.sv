module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// X equals (A1 & A2 & A3) | B1.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2 & A3) | B1)
    );

// B1 high forces X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

// A1, A2, and A3 high force X high.
    check_a_triplet_forces_x_high: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

// With B1 low, X equals A1 & A2 & A3.
    check_b1_low_reduces_to_and: assert property (
        @(posedge clk) !B1 |-> (X == (A1 & A2 & A3))
    );

// If X is low, then B1 is low and not all A inputs are high.
    check_x_low_implies_conditions: assert property (
        @(posedge clk) !X |-> (!B1 && !(A1 & A2 & A3))
    );

// If X is high, then B1 is high or all A inputs are high.
    check_x_high_implies_conditions: assert property (
        @(posedge clk) X |-> (B1 || (A1 & A2 & A3))
    );

endmodule
