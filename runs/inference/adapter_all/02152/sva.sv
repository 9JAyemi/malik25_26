module dynamic_gate_sva (
    input logic in,
    input logic clk,
    input logic out
);
    // Next-cycle out equals previous-cycle in (1-cycle latency).
    check_out_follows_prev_in: assert property (
        @(posedge clk) 1'b1 |-> ##1 (out == $past(in))
    );

    // If in was 1 last cycle, out is 1 now.
    check_out_high_when_prev_in_high: assert property (
        @(posedge clk) $past(in) |-> (out == 1'b1)
    );

    // If in was 0 last cycle, out is 0 now.
    check_out_low_when_prev_in_low: assert property (
        @(posedge clk) !$past(in) |-> (out == 1'b0)
    );

    // If out is 1 now, in was 1 last cycle.
    check_prev_in_high_when_out_high: assert property (
        @(posedge clk) out |-> $past(in)
    );

    // If out is 0 now, in was 0 last cycle.
    check_prev_in_low_when_out_low: assert property (
        @(posedge clk) !out |-> !$past(in)
    );

    // If in toggled between last two cycles, out toggles now.
    check_out_toggles_when_in_toggles: assert property (
        @(posedge clk) ($past(in) ^ $past(in,2)) |-> (out ^ $past(out))
    );

    // If in was stable over the last two cycles, out is stable now.
    check_out_stable_when_in_stable: assert property (
        @(posedge clk) ($past(in) == $past(in,2)) |-> (out == $past(out))
    );

    // If in was 1 last cycle and 0 two cycles ago, out is 1 now.
    check_out_high_when_prev1_high_prev2_low: assert property (
        @(posedge clk) ($past(in) && !$past(in,2)) |-> (out == 1'b1)
    );

    // If in was 0 last cycle and 1 two cycles ago, out is 0 now.
    check_out_low_when_prev1_low_prev2_high: assert property (
        @(posedge clk) (!$past(in) && $past(in,2)) |-> (out == 1'b0)
    );
endmodule