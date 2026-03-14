module multiplier_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] product
);
    // Product equals mathematical multiplication of a and b.
    check_product_equals_multiply: assert property (
        @(posedge clk) disable iff (1'b0) product == (a * b)
    );

    // If either input is zero then product is zero.
    check_zero_input_drives_zero_output: assert property (
        @(posedge clk) disable iff (1'b0) ((a == 4'd0) || (b == 4'd0)) |-> (product == 8'd0)
    );

    // If a is 1 then product equals b (zero-extended).
    check_identity_when_a_is_one: assert property (
        @(posedge clk) disable iff (1'b0) (a == 4'd1) |-> (product == {4'b0, b})
    );

    // If b is 1 then product equals a (zero-extended).
    check_identity_when_b_is_one: assert property (
        @(posedge clk) disable iff (1'b0) (b == 4'd1) |-> (product == {4'b0, a})
    );

    // Product never exceeds 15*15 = 225.
    check_product_upper_bound_225: assert property (
        @(posedge clk) disable iff (1'b0) product <= 8'd225
    );

    // LSB of product equals AND of LSBs of inputs.
    check_lsb_equals_and_of_lsbs: assert property (
        @(posedge clk) disable iff (1'b0) product[0] == (a[0] & b[0])
    );

    // If inputs are stable, product must be stable.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(a) && $stable(b)) |-> $stable(product)
    );

    // If product changes, at least one input must have changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) disable iff (1'b0) $changed(product) |-> ($changed(a) || $changed(b))
    );

    // Product equals sum of shifted partial products based on b bits.
    check_partial_product_expansion_matches: assert property (
        @(posedge clk) disable iff (1'b0)
            product == (
                (b[0] ? {4'b0, a}           : 8'd0) +
                (b[1] ? {3'b0, a, 1'b0}     : 8'd0) +
                (b[2] ? {2'b0, a, 2'b0}     : 8'd0) +
                (b[3] ? {1'b0, a, 3'b0}     : 8'd0)
            )
    );

    // Specific max case: 15*15 equals 225.
    check_specific_max_case_15x15: assert property (
        @(posedge clk) disable iff (1'b0) ((a == 4'd15) && (b == 4'd15)) |-> (product == 8'd225)
    );
endmodule