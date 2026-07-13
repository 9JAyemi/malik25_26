module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

// Sum is zero when reset is asserted.
    check_reset_clears_sum: assert property (
        @(posedge clk) reset |-> (sum == 32'h0000_0000)
    );

// With select low, sum is a plus b.
    check_select_low_adds: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |-> (sum == (a + b))
    );

// With select high, sum is a plus bitwise-not b.
    check_select_high_subtracts: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (sum == (a + ~b))
    );

// LSB of sum follows the RTL carry-out of the selected addition.
    check_lsb_follows_selected_carry: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (sum[0] == ((select ? (a + ~b) : (a + b))[0]))
    );

// When b is zero, sum passes a through regardless of select.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (b == 32'h0000_0000) |-> (sum == a)
    );

// When a is zero, sum passes b through regardless of select.
    check_a_zero_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (a == 32'h0000_0000) |-> (sum == b)
    );

// When a equals b, sum is zero regardless of select.
    check_equal_operands_zero: assert property (
        @(posedge clk) disable iff (reset)
        (a == b) |-> (sum == 32'h0000_0000)
    );

// When a equals bitwise-not b, sum is all ones regardless of select.
    check_complement_operands_ones: assert property (
        @(posedge clk) disable iff (reset)
        (a == ~b) |-> (sum == 32'hFFFF_FFFF)
    );

endmodule
