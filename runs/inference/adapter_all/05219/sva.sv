module xor_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic X,
    input logic VPWR,
    input logic VGND
);

    // X must equal the XOR of A and B.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // When both inputs are low, X must be low.
    check_both_low: assert property (
        @(posedge clk) (!A && !B) |-> !X
    );

    // When both inputs are high, X must be low.
    check_both_high: assert property (
        @(posedge clk) (A && B) |-> !X
    );

    // When A is low and B is high, X must be high.
    check_a_low_b_high: assert property (
        @(posedge clk) (!A && B) |-> X
    );

    // When A is high and B is low, X must be high.
    check_a_high_b_low: assert property (
        @(posedge clk) (A && !B) |-> X
    );

    // X can be high only when the inputs differ.
    check_x_high_requires_mismatch: assert property (
        @(posedge clk) X |-> (A ^ B)
    );

    // X can be low only when the inputs are equal.
    check_x_low_requires_match: assert property (
        @(posedge clk) !X |-> !(A ^ B)
    );

endmodule