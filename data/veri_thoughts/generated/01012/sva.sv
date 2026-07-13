module bitwise_or_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] X
);
    // Output equals the bitwise OR of inputs.
    check_or_function: assert property (
        @(posedge clk) X == (A | B)
    );

    // Output never has 1s where both inputs are 0.
    check_no_spurious_ones: assert property (
        @(posedge clk) (X & ~A & ~B) == 8'h00
    );

    // All 1s present in inputs appear on the output.
    check_no_missing_ones: assert property (
        @(posedge clk) ((A | B) & ~X) == 8'h00
    );

    // If A is zero, output equals B.
    check_zero_identity_A: assert property (
        @(posedge clk) (A == 8'h00) |-> (X == B)
    );

    // If B is zero, output equals A.
    check_zero_identity_B: assert property (
        @(posedge clk) (B == 8'h00) |-> (X == A)
    );

    // If both inputs are zero, output is zero.
    check_both_zero_yields_zero: assert property (
        @(posedge clk) ((A == 8'h00) && (B == 8'h00)) |-> (X == 8'h00)
    );

    // When inputs are stable across cycles, output is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) |-> $stable(X)
    );
endmodule