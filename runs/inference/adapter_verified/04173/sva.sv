module logic_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic X
);

// X equals (A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1).
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2) & (~B1 | B2) & (~A1 | ~A2 | B1))
    );

// If A1 and A2 are both 1, X must be 0.
    check_a1_a2_both_one_forces_zero: assert property (
        @(posedge clk) (A1 && A2) |-> (X == 1'b0)
    );

// If B1 is 1 and B2 is 0, X must be 0.
    check_b1_one_b2_zero_forces_zero: assert property (
        @(posedge clk) (B1 && !B2) |-> (X == 1'b0)
    );

// If A1 is 0 and A2 is 0, X must be 0.
    check_a1_a2_zero_forces_zero: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == 1'b0)
    );

// If B1 is 0 and B2 is 1, X must be 1.
    check_b1_zero_b2_one_sets_one: assert property (
        @(posedge clk) (!B1 && B2) |-> (X == 1'b1)
    );

// If A1 is 1 and B1 is 0, X must be 0.
    check_a1_one_b1_zero_forces_zero: assert property (
        @(posedge clk) (A1 && !B1) |-> (X == 1'b0)
    );

// If A1 is 0 and B1 is 1, X must be 1.
    check_a1_zero_b1_one_sets_one: assert property (
        @(posedge clk) (!A1 && B1) |-> (X == 1'b1)
    );

// If A2 is 1 and B1 is 0, X must be 0.
    check_a2_one_b1_zero_forces_zero: assert property (
        @(posedge clk) (A2 && !B1) |-> (X == 1'b0)
    );

// If A2 is 0 and B1 is 1, X must be 1.
    check_a2_zero_b1_one_sets_one: assert property (
        @(posedge clk) (!A2 && B1) |-> (X == 1'b1)
    );

endmodule
