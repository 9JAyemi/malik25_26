module multiplier_sva (
    input logic        clk,
    input logic        rst,     // Active-HIGH asynchronous reset
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] Z
);
    // Clock: posedge clk. Reset: rst (active-high, async). Sequential: Z registered; Z<=0 on reset else Z<=A*B.

    // While reset is held across consecutive clock edges, Z must be 0.
    check_zero_while_reset_held: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (Z == 16'd0)
    );

    // After any cycle where reset is asserted, Z must be 0 on the next clock edge.
    check_reset_assert_drives_zero_next: assert property (
        @(posedge clk) rst |=> (Z == 16'd0)
    );

    // On the cycle reset deasserts, Z must still be 0 (was forced by reset in the prior cycle).
    check_zero_on_reset_release_edge: assert property (
        @(posedge clk) $fell(rst) |-> (Z == 16'd0)
    );

    // While reset remains asserted across cycles, Z does not change.
    check_zero_stable_while_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (Z == $past(Z))
    );
endmodule