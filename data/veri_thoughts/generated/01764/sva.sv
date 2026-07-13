module top_module_sva (
    input  logic        clk,
    input  logic        reset,   // active-high synchronous
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    input  logic [7:0]  q
);

    ///// Reset behavior /////
    // When reset is asserted, q must be 0.
    reset_q_zero: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

    ///// Output selection rules /////
    // If a<b, q must equal a.
    q_matches_a_when_a_lt_b: assert property (
        @(posedge clk) disable iff (reset) (a < b) |-> (q == a)
    );

    // If a<b, q is strictly less than b.
    q_lt_b_when_a_lt_b: assert property (
        @(posedge clk) disable iff (reset) (a < b) |-> (q < b)
    );

    // If a>b, q comes from 4-bit counter, so upper nibble is zero.
    q_upper_nibble_zero_when_a_gt_b: assert property (
        @(posedge clk) disable iff (reset) (a > b) |-> (q[7:4] == 4'b0000)
    );

    // If a>=b, q is from counter or sum, so q <= 16.
    q_bounded_when_a_ge_b: assert property (
        @(posedge clk) disable iff (reset) (a >= b) |-> (q <= 8'h10)
    );

    // If a==b, q equals count + a[0], so q >= a[0].
    q_min_bound_when_equal: assert property (
        @(posedge clk) disable iff (reset) (a == b) |-> (q >= {7'b0, a[0]})
    );

    // If a==b and a[0]==0, q equals count (0..15).
    q_max_15_when_equal_a0_zero: assert property (
        @(posedge clk) disable iff (reset) (a == b) && (a[0] == 1'b0) |-> (q <= 8'h0F)
    );

    ///// Cross-cycle behaviors /////
    // If a>b in two consecutive cycles, q's low nibble increments by 1 (mod 16) and upper nibble stays zero.
    gt_consecutive_incr_low_nibble: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(a) > $past(b)) && (a > b))
            |-> ($past(q[7:4]) == 4'b0000) && (q[7:4] == 4'b0000) && (q[3:0] == $past(q[3:0]) + 4'd1)
    );

    // If a==b in two consecutive cycles and a[0] is stable, q's low nibble increments by 1 (mod 16).
    eq_consecutive_incr_low_nibble_a0_stable: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(a) == $past(b)) && (a == b) && ($past(a[0]) == a[0]))
            |-> (q[3:0] == $past(q[3:0]) + 4'd1)
    );

    ///// Range disambiguation /////
    // If a>=b and q>15, it must be the equal-path producing exactly 16.
    high_value_only_on_equal_16: assert property (
        @(posedge clk) disable iff (reset)
            ((a >= b) && (q > 8'h0F)) |-> ((a == b) && (q == 8'h10))
    );

endmodule