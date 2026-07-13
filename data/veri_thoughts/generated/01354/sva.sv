module multiplier_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);
    // When both inputs have MSB=1, result is bitwise-not of product plus one.
    check_both_negative: assert property (
        @(posedge clk) (a[7] && b[7]) |-> (result == (~(a*b) + 1))
    );

    // When both inputs have MSB=0, result equals the product.
    check_both_positive: assert property (
        @(posedge clk) (!a[7] && !b[7]) |-> (result == (a*b))
    );

    // When inputs have different MSBs, result equals negative of the product.
    check_different_signs: assert property (
        @(posedge clk) (a[7] ^ b[7]) |-> (result == -(a*b))
    );

    // Multiplication by zero yields zero regardless of signs.
    check_zero_multiplication: assert property (
        @(posedge clk) ((a == 8'd0) || (b == 8'd0)) |-> (result == 16'd0)
    );

    // Result always matches the piecewise function implemented in RTL.
    check_piecewise_definition: assert property (
        @(posedge clk)
            result == ((a[7] && b[7]) ? (~(a*b) + 1) :
                       ((!a[7] && !b[7]) ? (a*b) : (-(a*b))))
    );

    // If inputs are unchanged across a cycle, result is unchanged.
    check_stable_inputs_imply_stable_result: assert property (
        @(posedge clk) ((a == $past(a)) && (b == $past(b))) |-> (result == $past(result))
    );

    // Swapping inputs across consecutive cycles leaves result unchanged (commutativity).
    check_commutativity_across_cycles: assert property (
        @(posedge clk) ((a == $past(b)) && (b == $past(a))) |-> (result == $past(result))
    );
endmodule