module logic_gate_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic X
);
    ///// Combinational function checks /////
    // X must be 1 iff A1 & A2 & (B1 | B2) & ~C1 is 1.
    check_function_implies_x: assert property (
        @(posedge CLK) (A1 & A2 & (B1 | B2) & ~C1) |-> (X == 1'b1)
    );
    // If X is 1, all enabling conditions must be true.
    check_x_implies_function: assert property (
        @(posedge CLK) (X == 1'b1) |-> (A1 & A2 & (B1 | B2) & ~C1)
    );

    ///// Blocking conditions /////
    // If C1 is HIGH, X must be 0.
    check_c1_blocks_x: assert property (
        @(posedge CLK) C1 |-> (X == 1'b0)
    );
    // If A1 is LOW, X must be 0.
    check_a1_low_blocks_x: assert property (
        @(posedge CLK) !A1 |-> (X == 1'b0)
    );
    // If A2 is LOW, X must be 0.
    check_a2_low_blocks_x: assert property (
        @(posedge CLK) !A2 |-> (X == 1'b0)
    );
    // If both B1 and B2 are LOW, X must be 0.
    check_b_both_low_blocks_x: assert property (
        @(posedge CLK) (!B1 & !B2) |-> (X == 1'b0)
    );

    ///// Necessary conditions when X is HIGH /////
    // If X is HIGH, at least one of B1 or B2 must be HIGH.
    check_x_requires_b: assert property (
        @(posedge CLK) X |-> (B1 | B2)
    );
    // If X is HIGH, A1 and A2 must be HIGH and C1 must be LOW.
    check_x_requires_a1_a2_c1: assert property (
        @(posedge CLK) X |-> (A1 & A2 & ~C1)
    );
endmodule