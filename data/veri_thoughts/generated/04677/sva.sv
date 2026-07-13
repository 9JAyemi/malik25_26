module xor_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // y must implement the XOR of a and b.
    check_xor_function: assert property (
        @(posedge clk) y == (a ^ b)
    );

    // When both inputs are low, y must be low.
    check_y_low_for_00: assert property (
        @(posedge clk) (!a && !b) |-> !y
    );

    // When only b is high, y must be high.
    check_y_high_for_01: assert property (
        @(posedge clk) (!a && b) |-> y
    );

    // When only a is high, y must be high.
    check_y_high_for_10: assert property (
        @(posedge clk) (a && !b) |-> y
    );

    // When both inputs are high, y must be low.
    check_y_low_for_11: assert property (
        @(posedge clk) (a && b) |-> !y
    );

endmodule