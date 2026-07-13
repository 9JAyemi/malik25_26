module two_input_inv_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic y
);

    // Output implements the RTL equation y = ~a & ~b.
    check_output_equation: assert property (
        @(posedge clk) y == (~a & ~b)
    );

    // When both inputs are low, the output must be high.
    check_both_low_drive_high: assert property (
        @(posedge clk) (!a && !b) |-> y
    );

    // A high on input a forces the output low.
    check_a_high_drives_low: assert property (
        @(posedge clk) a |-> !y
    );

    // A high on input b forces the output low.
    check_b_high_drives_low: assert property (
        @(posedge clk) b |-> !y
    );

endmodule