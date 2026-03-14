module OR_gate_pipeline_sva (
    input logic a,
    input logic b,
    input logic clk,
    input logic out,
    input logic p1_out
);
    // Out captures p1_out on the next rising clock.
    check_out_captures_p1_out_next: assert property (
        @(posedge clk) 1'b1 |-> ##1 (out == $past(p1_out))
    );

    // If p1_out is 1 at a clock, out is 1 next clock.
    check_out_follows_p1_out_high: assert property (
        @(posedge clk) p1_out |-> ##1 (out == 1'b1)
    );

    // If p1_out is 0 at a clock, out is 0 next clock.
    check_out_follows_p1_out_low: assert property (
        @(posedge clk) !p1_out |-> ##1 (out == 1'b0)
    );

    // A rising out implies previous p1_out was 1.
    check_out_rise_implies_prev_p1_high: assert property (
        @(posedge clk) $rose(out) |-> $past(p1_out) == 1'b1
    );

    // A falling out implies previous p1_out was 0.
    check_out_fall_implies_prev_p1_low: assert property (
        @(posedge clk) $fell(out) |-> $past(p1_out) == 1'b0
    );

    // When a,b stable since last clock, p1_out equals a|b at this clock.
    check_p1_out_matches_or_when_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> (p1_out == (a | b))
    );

    // When a,b stable since last clock, next out equals current a|b.
    check_out_next_matches_or_when_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> ##1 (out == $past(a | b))
    );

    // When a==b and stable, p1_out equals a (idempotent OR).
    check_p1_out_idempotent_when_equal_and_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && (a == b)) |-> (p1_out == a)
    );

    // When a=b=0 and stable, next out is 0.
    check_zero_propagates_to_out_when_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && (a == 1'b0) && (b == 1'b0)) |-> ##1 (out == 1'b0)
    );

    // When a|b==1 and inputs stable, next out is 1.
    check_one_propagates_to_out_when_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && ((a | b) == 1'b1)) |-> ##1 (out == 1'b1)
    );
endmodule