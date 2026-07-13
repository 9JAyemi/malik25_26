module and_gate_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out
);
    // Clock: clk (posedge). No reset in RTL. Mixed logic: comb AND into a DFF, out is reg'd AND (1-cycle delay).

    // Out equals AND of inputs delayed by 1 clock.
    check_out_is_delayed_and: assert property (
        @(posedge clk) 1'b1 |-> ##1 (out == $past(a & b))
    );

    // If both inputs are 1 at a clock, out is 1 on the next clock.
    check_next_out_one_when_both_one: assert property (
        @(posedge clk) (a && b) |-> ##1 (out == 1'b1)
    );

    // If either input is 0 at a clock, out is 0 on the next clock.
    check_next_out_zero_when_either_zero: assert property (
        @(posedge clk) (!(a && b)) |-> ##1 (out == 1'b0)
    );

    // A rising edge on out implies previous cycle had a&b == 1.
    check_out_rise_only_if_prev_and_one: assert property (
        @(posedge clk) $rose(out) |-> $past(a && b)
    );

    // A falling edge on out implies previous cycle had a&b == 0.
    check_out_fall_only_if_prev_and_zero: assert property (
        @(posedge clk) $fell(out) |-> !$past(a && b)
    );

    // If out changes this cycle, then (a&b) changed in the previous cycle.
    check_out_change_implies_prev_and_change: assert property (
        @(posedge clk) (out != $past(out)) |-> ($past(a & b, 2) != $past(a & b))
    );

    // If (a&b) changes this cycle, out changes on the next cycle.
    check_prev_and_change_implies_out_change: assert property (
        @(posedge clk) ((a & b) != $past(a & b)) |-> ##1 (out != $past(out))
    );

    // If inputs are stable across a clock, out is stable across the next clock.
    check_stability_propagation: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> ##1 ($stable(out))
    );
endmodule