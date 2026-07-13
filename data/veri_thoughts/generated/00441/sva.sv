module binary_multiplier_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);

    // Result must equal the current product of the inputs.
    check_result_matches_product: assert property (
        @(posedge clk) result == ($unsigned(a) * $unsigned(b))
    );

    // A zero operand must force the product to zero.
    check_zero_operand_forces_zero_result: assert property (
        @(posedge clk) ((a == 8'd0) || (b == 8'd0)) |-> (result == 16'd0)
    );

    // Multiplying by one on a must pass b through to the result.
    check_a_one_passthroughs_b: assert property (
        @(posedge clk) (a == 8'd1) |-> (result == {8'd0, b})
    );

    // Multiplying by one on b must pass a through to the result.
    check_b_one_passthroughs_a: assert property (
        @(posedge clk) (b == 8'd1) |-> (result == {8'd0, a})
    );

    // If both inputs are stable, the result must also remain stable.
    check_result_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(result)
    );

    // The product LSB must equal the AND of the input LSBs.
    check_lsb_matches_input_lsbs: assert property (
        @(posedge clk) result[0] == (a[0] & b[0])
    );

endmodule