module sky130_fd_sc_lp__o21a_sva (
    input  logic clk,
    input  logic X,
    input  logic A1,
    input  logic A2,
    input  logic B1,
    input  logic VPWR,
    input  logic VGND,
    input  logic VPB,
    input  logic VNB
);
    // X matches the RTL sum-of-terms definition using 4-state comparisons.
    check_function_equivalence: assert property (
        @(posedge clk)
        X === ((A1 == 1'b1) || ((A1 == 1'b0) && (A2 == 1'b1)) || ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b1)))
    );

    // If A1 is 1, X must be 1.
    check_a1_one_forces_x_one: assert property (
        @(posedge clk)
        (A1 === 1'b1) |-> (X === 1'b1)
    );

    // If A1 is 0 and A2 is 1, X must be 1.
    check_a1_zero_a2_one_forces_x_one: assert property (
        @(posedge clk)
        ((A1 === 1'b0) && (A2 === 1'b1)) |-> (X === 1'b1)
    );

    // If A1 is 0, A2 is 0, and B1 is 1, X must be 1.
    check_a1_zero_a2_zero_b1_one_forces_x_one: assert property (
        @(posedge clk)
        ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b1)) |-> (X === 1'b1)
    );

    // If A1, A2, and B1 are all 0, X must be 0.
    check_all_zeros_force_x_zero: assert property (
        @(posedge clk)
        ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b0)) |-> (X === 1'b0)
    );

    // If X is 0, then A1, A2, and B1 must all be 0.
    check_x_zero_implies_all_zero_inputs: assert property (
        @(posedge clk)
        (X === 1'b0) |-> ((A1 === 1'b0) && (A2 === 1'b0) && (B1 === 1'b0))
    );

    // With all inputs known (0/1), X must also be known (not X/Z).
    check_known_inputs_imply_known_x: assert property (
        @(posedge clk)
        (!$isunknown({A1, A2, B1})) |-> (!$isunknown(X))
    );

    // With all inputs known (0/1), X equals bitwise OR of A1, A2, and B1.
    check_known_inputs_or_equivalence: assert property (
        @(posedge clk)
        (!$isunknown({A1, A2, B1})) |-> (X == (A1 | A2 | B1))
    );

    // If X is 1 while A1=0 and A2=0, then B1 must be 1.
    check_x_one_a1_zero_a2_zero_implies_b1_one: assert property (
        @(posedge clk)
        ((X === 1'b1) && (A1 === 1'b0) && (A2 === 1'b0)) |-> (B1 === 1'b1)
    );

    // If X is 1 and A1=0, then either A2=1 or (A2=0 and B1=1).
    check_x_one_a1_zero_requires_a2_one_or_b1_one: assert property (
        @(posedge clk)
        ((X === 1'b1) && (A1 === 1'b0)) |-> ((A2 === 1'b1) || ((A2 === 1'b0) && (B1 === 1'b1)))
    );
endmodule