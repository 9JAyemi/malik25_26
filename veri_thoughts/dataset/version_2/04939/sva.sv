module top_module_assertions (
    input logic clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic [31:0] sum
);

    // Output always matches 32-bit addition of a and b.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (a + b)
    );

    // With sub low, the output matches addition.
    check_add_mode_matches_addition: assert property (
        @(posedge clk) !sub |-> (sum == (a + b))
    );

    // With sub high, the output still matches addition.
    check_sub_mode_still_matches_addition: assert property (
        @(posedge clk) sub |-> (sum == (a + b))
    );

    // The low 16 bits match the low-half addition result.
    check_low_half_matches_addition: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

    // A carry from the low half increments the high-half result.
    check_high_half_with_low_carry: assert property (
        @(posedge clk)
        (({1'b0, a[15:0]} + {1'b0, b[15:0]}) >= 17'h1_0000)
        |-> (sum[31:16] == (a[31:16] + b[31:16] + 16'd1))
    );

    // Without a low-half carry, the high half is a simple add.
    check_high_half_without_low_carry: assert property (
        @(posedge clk)
        (({1'b0, a[15:0]} + {1'b0, b[15:0]}) < 17'h1_0000)
        |-> (sum[31:16] == (a[31:16] + b[31:16]))
    );

    // Zero on a passes b through to the output.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (a == 32'd0) |-> (sum == b)
    );

    // Zero on b passes a through to the output.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (b == 32'd0) |-> (sum == a)
    );

    // Changing sub alone does not change the output.
    check_sub_toggle_no_effect: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $changed(sub)) |-> $stable(sum)
    );

endmodule