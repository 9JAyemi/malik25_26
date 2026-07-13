module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // Output must match the AND of both inputs.
    check_and_function: assert property (
        @(posedge clk) y == (a & b)
    );

    // If input a is low, the output must be low.
    check_a_low_forces_y_low: assert property (
        @(posedge clk) !a |-> !y
    );

    // If input b is low, the output must be low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) !b |-> !y
    );

    // If both inputs are high, the output must be high.
    check_both_high_drives_y_high: assert property (
        @(posedge clk) (a && b) |-> y
    );

    // A high output requires both inputs to be high.
    check_y_high_implies_both_high: assert property (
        @(posedge clk) y |-> (a && b)
    );

endmodule