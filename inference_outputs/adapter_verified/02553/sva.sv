module binary_multiplier_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);

// Result must equal the 8-bit a times 8-bit b product.
    check_result_matches_product: assert property (
        @(posedge clk) result == ({8'b0, a} * {8'b0, b})
    );

// Zero on a must force the result to zero.
    check_zero_a_clears_result: assert property (
        @(posedge clk) (a == 8'h00) |-> (result == 16'h0000)
    );

// Zero on b must force the result to zero.
    check_zero_b_clears_result: assert property (
        @(posedge clk) (b == 8'h00) |-> (result == 16'h0000)
    );

// Maximum 8-bit values must produce the 16-bit maximum product.
    check_max_values_max_product: assert property (
        @(posedge clk) ((a == 8'hFF) && (b == 8'hFF)) |-> (result == 16'hFFFF)
    );

// Multiplying by 1 on b must pass a through to the result.
    check_b_one_passthrough: assert property (
        @(posedge clk) (b == 8'h01) |-> (result == {8'b0, a})
    );

// Multiplying by 1 on a must pass b through to the result.
    check_a_one_passthrough: assert property (
        @(posedge clk) (a == 8'h01) |-> (result == {8'b0, b})
    );

endmodule
