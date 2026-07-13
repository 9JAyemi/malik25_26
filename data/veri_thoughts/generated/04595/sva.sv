module Adder_with_reset_sva (
    input logic [3:0] A,
    input logic       B,
    input logic       RST,
    input logic       clk,
    input logic [4:0] Q
);

    // A reset cycle clears Q.
    check_reset_clears_q: assert property (
        @(posedge clk) disable iff (RST || $initstate)
        $past(RST) |-> (Q == 5'd0)
    );

    // Q stores the previous cycle's zero-extended 4-bit sum when not in reset.
    check_q_matches_registered_sum: assert property (
        @(posedge clk) disable iff (RST || $initstate)
        !$past(RST) |-> (Q == {1'b0, ($past(A) + $past(B))})
    );

    // The MSB of Q is always zero after an update.
    check_q_msb_zero: assert property (
        @(posedge clk) disable iff (RST || $initstate)
        1'b1 |-> (Q[4] == 1'b0)
    );

    // With B low, Q passes through the previous A value.
    check_b_zero_passthrough: assert property (
        @(posedge clk) disable iff (RST || $initstate)
        (!$past(RST) && ($past(B) == 1'b0)) |-> (Q == {1'b0, $past(A)})
    );

    // Adding 1 to 4'hF wraps in the 4-bit sum stored into Q.
    check_wrap_on_max_plus_one: assert property (
        @(posedge clk) disable iff (RST || $initstate)
        (!$past(RST) && ($past(A) == 4'hF) && ($past(B) == 1'b1)) |-> (Q == 5'd0)
    );

endmodule