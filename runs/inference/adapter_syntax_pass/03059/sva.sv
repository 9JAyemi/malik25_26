module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic select,
    input logic [31:0] sum
);

    // Reset forces the registered output to zero.
    check_reset_clears_sum: assert property (
        @(posedge clk) reset |-> (sum == 32'h00000000)
    );

    // With select low, the output is the 32-bit sum of a and b.
    check_select_low_adds_inputs: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |-> (sum == ((a + b) & 32'h00000000FFFFFFFF))
    );

    // With select high, the output is the 32-bit difference a - b.
    check_select_high_subtracts_inputs: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (sum == ((a - b) & 32'h00000000FFFFFFFF))
    );

    // Zero on b passes a through when select is low.
    check_zero_b_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (!select && (b == 32'h00000000)) |-> (sum == a)
    );

    // Zero on a makes the output equal to the inverted b when select is high.
    check_zero_a_inverts_b: assert property (
        @(posedge clk) disable iff (reset)
        (select && (a == 32'h00000000)) |-> (sum == (~b))
    );

    // Equal operands cancel each other when select is high.
    check_equal_operands_cancel: assert property (
        @(posedge clk) disable iff (reset)
        (select && (a == b)) |-> (sum == 32'h00000000)
    );

    // Stable inputs keep the registered output stable across cycles.
    check_stable_inputs_hold_sum: assert property (
        @(posedge clk) disable iff (reset)
        ($stable(a) && $stable(b) && $stable(select)) |-> $stable(sum)
    );

endmodule