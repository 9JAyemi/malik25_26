module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

// X equals (A1 & A2) | B1 | C1.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

// If B1 is HIGH, X must be HIGH.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

// If C1 is HIGH, X must be HIGH.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

// If A1 and A2 are both HIGH, X must be HIGH.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

// If B1 and C1 are LOW and A1/A2 are not both HIGH, X must be LOW.
    check_no_active_input_means_x_low: assert property (
        @(posedge clk) (!B1 && !C1 && !(A1 && A2)) |-> !X
    );

// If X is LOW, then B1, C1, and (A1 & A2) must all be LOW.
    check_x_low_implies_inputs_low: assert property (
        @(posedge clk) !X |-> (!B1 && !C1 && !(A1 && A2))
    );

endmodule
