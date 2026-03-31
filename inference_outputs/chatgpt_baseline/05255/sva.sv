module binary_multiplier_assertions (
    input logic clk,
    input logic reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);

    // Reset clears the registered result on the following cycle.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 32'd0)
    );

    // Outside reset, result matches the previous cycle's product.
    check_product_update: assert property (
        @(posedge clk) disable iff (reset)
        (!reset) |=> (result == ($past(a) * $past(b)))
    );

    // A zero multiplicand produces a zero result on the following cycle.
    check_zero_multiplicand: assert property (
        @(posedge clk) disable iff (reset)
        ((a == 16'd0) || (b == 16'd0)) |=> (result == 32'd0)
    );

    // Multiplying by one on a passes b through to result.
    check_a_is_one: assert property (
        @(posedge clk) disable iff (reset)
        (a == 16'd1) |=> (result == {16'd0, $past(b)})
    );

    // Multiplying by one on b passes a through to result.
    check_b_is_one: assert property (
        @(posedge clk) disable iff (reset)
        (b == 16'd1) |=> (result == {16'd0, $past(a)})
    );

    // Maximum 16-bit inputs produce the expected 32-bit product.
    check_max_times_max: assert property (
        @(posedge clk) disable iff (reset)
        ((a == 16'hFFFF) && (b == 16'hFFFF)) |=> (result == 32'hFFFE0001)
    );

endmodule