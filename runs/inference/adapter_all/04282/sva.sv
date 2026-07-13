module my_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y matches the implemented combinational function.
    check_y_function: assert property (
        @(posedge clk) Y == ~((A1 & A2 & B1) | (A1 & B1))
    );

    // A high Y requires B1 to be low.
    check_y_high_requires_b1_low: assert property (
        @(posedge clk) Y |-> !B1
    );

    // B1 high forces Y low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // With B1 low, Y reduces to the inverse of A1 & A2.
    check_b1_low_reduces_to_not_a1_a2: assert property (
        @(posedge clk) !B1 |-> (Y == ~(A1 & A2))
    );

    // If A1 and A2 are both high, Y must be low.
    check_a1_a2_high_force_y_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // With B1 low and A1 low, Y must be high.
    check_b1_low_a1_low_forces_y_high: assert property (
        @(posedge clk) (!B1 & !A1) |-> Y
    );

    // With B1 low and A2 low, Y must be high.
    check_b1_low_a2_low_forces_y_high: assert property (
        @(posedge clk) (!B1 & !A2) |-> Y
    );

    // With B1 low and A1 high, Y equals the inverse of A2.
    check_b1_low_a1_high_reduces_to_not_a2: assert property (
        @(posedge clk) (!B1 & A1) |-> (Y == ~A2)
    );

    // With B1 low and A2 high, Y equals the inverse of A1.
    check_b1_low_a2_high_reduces_to_not_a1: assert property (
        @(posedge clk) (!B1 & A2) |-> (Y == ~A1)
    );

endmodule