module custom_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1
);

    // X must match the XOR of A1 and A2 gated by B1.
    check_x_matches_xor_gate: assert property (
        @(posedge clk) X == ((A1 ^ A2) & B1)
    );

    // B1 low forces X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // With B1 high, X reduces to A1 XOR A2.
    check_b1_high_reduces_to_xor: assert property (
        @(posedge clk) B1 |-> (X == (A1 ^ A2))
    );

    // Equal A inputs force X low.
    check_equal_a_inputs_force_x_low: assert property (
        @(posedge clk) !(A1 ^ A2) |-> !X
    );

    // Different A inputs make X follow B1.
    check_different_a_inputs_follow_b1: assert property (
        @(posedge clk) (A1 ^ A2) |-> (X == B1)
    );

    // X high requires B1 high and A1 different from A2.
    check_x_high_requires_b1_and_mismatch: assert property (
        @(posedge clk) X |-> (B1 && (A1 ^ A2))
    );

endmodule