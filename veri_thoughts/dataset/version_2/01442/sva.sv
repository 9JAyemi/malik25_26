module arithmetic_sva (
    input logic CLK,
    input logic signed [7:0] A,
    input logic signed [7:0] B,
    input logic signed [7:0] sum,
    input logic signed [7:0] diff,
    input logic signed [15:0] product,
    input logic signed [7:0] quotient
);
    // Sum must equal A + B (8-bit signed)
    check_sum_equals_A_plus_B: assert property (
        @(posedge CLK) sum == (A + B)
    );

    // Diff must equal A - B (8-bit signed)
    check_diff_equals_A_minus_B: assert property (
        @(posedge CLK) diff == (A - B)
    );

    // Product must equal A * B (16-bit signed)
    check_product_equals_A_times_B: assert property (
        @(posedge CLK) product == (A * B)
    );

    // When divisor is zero, quotient must be zero
    check_quotient_zero_when_div_by_zero: assert property (
        @(posedge CLK) (B == 0) |-> (quotient == 0)
    );

    // When divisor is nonzero, quotient must be A / B (8-bit signed)
    check_quotient_equals_A_div_B_when_B_nonzero: assert property (
        @(posedge CLK) (B != 0) |-> (quotient == (A / B))
    );

    // If A is zero, product must be zero
    check_product_zero_if_A_zero: assert property (
        @(posedge CLK) (A == 0) |-> (product == 0)
    );

    // If B is zero, product must be zero
    check_product_zero_if_B_zero: assert property (
        @(posedge CLK) (B == 0) |-> (product == 0)
    );

    // Outputs must be stable when inputs are stable (pure combinational behavior)
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> ($stable(sum) && $stable(diff) && $stable(product) && $stable(quotient))
    );
endmodule