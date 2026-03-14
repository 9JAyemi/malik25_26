module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count,
    input logic max
);
    // On synchronous reset, drive count=0 and max=0.
    reset_outputs_zero: assert property (
        @(posedge clk) rst |-> (count == 4'd0) && (max == 1'b0)
    );

    // If prev cycle not in reset and prev count!=11, increment and keep max=0.
    incr_when_prev_not_11: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            ($past(!rst) && ($past(count) != 4'd11)) |-> (count == ($past(count) + 4'd1)) && (max == 1'b0)
    );

    // If prev cycle not in reset and prev count==11, wrap to 0 and set max=1.
    wrap_when_prev_is_11: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            ($past(!rst) && ($past(count) == 4'd11)) |-> (count == 4'd0) && (max == 1'b1)
    );

    // max can be 1 only when previous count was 11 (and prev not in reset).
    max_only_when_prev_11: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            max |-> ($past(!rst) && ($past(count) == 4'd11))
    );

    // Whenever max=1, the current count must be 0.
    max_implies_zero_count: assert property (
        @(posedge clk) disable iff (rst)
            max |-> (count == 4'd0)
    );

    // When current count is 0, max reflects whether previous count was 11.
    zero_count_encodes_prev: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (count == 4'd0) |-> (max == ($past(count) == 4'd11))
    );

    // Count transition is only prev+1 or wrap from 11 to 0 (when prev not in reset).
    count_transition_valid: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            $past(!rst) |-> ((($past(count) == 4'd11) && (count == 4'd0)) ||
                             (($past(count) != 4'd11) && (count == ($past(count) + 4'd1))))
    );

    // max is a single-cycle pulse (cannot be high in consecutive cycles).
    max_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            max |=> !max
    );

    // When current count is 11, max must be 0.
    max_low_when_count_11: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (count == 4'd11) |-> (max == 1'b0)
    );

    // After a wrap cycle (count=0,max=1), next cycle increments to 1 and clears max (or reset intervenes).
    next_after_wrap_increments: assert property (
        @(posedge clk) disable iff (rst || $initstate)
            (count == 4'd0 && max == 1'b1) |=> (rst || (count == 4'd1 && max == 1'b0))
    );
endmodule