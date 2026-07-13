module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X must match the implemented OR-of-three function.
    check_output_function: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // C1 high must force X high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together must force X high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // With B1 and C1 low, X must equal A1 AND A2.
    check_no_b1_c1_reduces_to_and: assert property (
        @(posedge clk) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // With A1 and A2 low, X must equal B1 OR C1.
    check_no_a1_a2_reduces_to_or: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == (B1 | C1))
    );

    // If X is low, then B1 and C1 must be low and not both A inputs high.
    check_x_low_implies_inputs: assert property (
        @(posedge clk) !X |-> (!B1 && !C1 && !(A1 && A2))
    );

endmodule