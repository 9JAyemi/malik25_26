module top_module_sva (
    input logic clk,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [15:0] product
);
    // Product must equal num1 * num2 every cycle.
    check_product_matches_multiply: assert property (
        @(posedge clk) product == (num1 * num2)
    );

    // If inputs are stable, product must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(num1) && $stable(num2) |-> $stable(product)
    );

    // If product changes, at least one input must have changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(product) |-> ($changed(num1) || $changed(num2))
    );

    // If num1 is zero, product must be zero.
    check_zero_multiplicand1: assert property (
        @(posedge clk) (num1 == 8'd0) |-> (product == 16'd0)
    );

    // If num2 is zero, product must be zero.
    check_zero_multiplicand2: assert property (
        @(posedge clk) (num2 == 8'd0) |-> (product == 16'd0)
    );

    // If product is zero, at least one operand must be zero.
    check_zero_product_implies_zero_operand: assert property (
        @(posedge clk) (product == 16'd0) |-> ((num1 == 8'd0) || (num2 == 8'd0))
    );

    // If num1 is one, product equals num2 (zero-extended to 16 bits).
    check_one_multiplicand1: assert property (
        @(posedge clk) (num1 == 8'd1) |-> (product == {8'd0, num2})
    );

    // If num2 is one, product equals num1 (zero-extended to 16 bits).
    check_one_multiplicand2: assert property (
        @(posedge clk) (num2 == 8'd1) |-> (product == {8'd0, num1})
    );

    // LSB of product equals AND of operand LSBs.
    check_lsb_is_and: assert property (
        @(posedge clk) product[0] == (num1[0] & num2[0])
    );

    // If num1 is two, product equals num2 << 1.
    check_mul_by_two_num1: assert property (
        @(posedge clk) (num1 == 8'd2) |-> (product == ({8'd0, num2} << 1))
    );

    // If num2 is two, product equals num1 << 1.
    check_mul_by_two_num2: assert property (
        @(posedge clk) (num2 == 8'd2) |-> (product == ({8'd0, num1} << 1))
    );

    // Commutativity consistency: product equals num2 * num1 as well.
    check_commutativity_consistency: assert property (
        @(posedge clk) product == (num2 * num1)
    );

    // If num2 is 0xFF, product equals (num1<<8) - num1.
    check_mul_by_ff_decomposition: assert property (
        @(posedge clk) (num2 == 8'hFF) |-> (product == (({8'd0, num1} << 8) - {8'd0, num1}))
    );
endmodule