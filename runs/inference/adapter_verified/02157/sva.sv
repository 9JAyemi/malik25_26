module custom_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

// X equals (A1 ^ A2) & B1.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 ^ A2) & B1)
    );

// B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

// Equal A1/A2 inputs force X low.
    check_equal_inputs_force_x_low: assert property (
        @(posedge clk) (A1 == A2) |-> !X
    );

// Different A1/A2 inputs with B1 high drive X high.
    check_different_inputs_with_b1_high_drive_x_high: assert property (
        @(posedge clk) (A1 != A2) && B1 |-> X
    );

// X high implies B1 is high.
    check_x_high_implies_b1_high: assert property (
        @(posedge clk) X |-> B1
    );

// X high implies A1 and A2 differ.
    check_x_high_implies_inputs_different: assert property (
        @(posedge clk) X |-> (A1 != A2)
    );

endmodule
