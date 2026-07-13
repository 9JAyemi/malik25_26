module binary_counter_sva (
    input logic clk,
    input logic EN,
    input logic RST,
    input logic [3:0] COUNT
);
    // While reset is asserted (active-low), COUNT must be 0.
    reset_forces_zero: assert property (
        @(posedge clk) (RST == 1'b0) |-> (COUNT == 4'b0000)
    );

    // On reset deassertion, COUNT becomes 0 in the same cycle.
    reset_release_clears: assert property (
        @(posedge clk) $rose(RST) |-> (COUNT == 4'b0000)
    );

    // With EN=1 and not in reset, COUNT increments by 1 (mod 16).
    count_increments_when_en: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b1) |-> (COUNT == $past(COUNT) + 4'd1)
    );

    // With EN=0 and not in reset, COUNT holds its value.
    count_holds_when_en0: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b0) |-> (COUNT == $past(COUNT))
    );

    // Any change in COUNT (excluding reset) requires EN=1 in the prior cycle.
    change_requires_prev_en: assert property (
        @(posedge clk) disable iff (!RST) (COUNT != $past(COUNT)) |-> ($past(EN) == 1'b1)
    );

    // If EN=1 and not in reset, COUNT must change (no wrap at 15->0).
    en_implies_change_no_wrap: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b1) |-> (COUNT != $past(COUNT))
    );

    // If EN=0 and not in reset, COUNT must not change.
    en0_implies_no_change: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b0) |-> (COUNT == $past(COUNT))
    );

    // If EN=1 and COUNT is 15 (not in reset), next COUNT wraps to 0.
    wrap_on_max_when_en: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b1 && COUNT == 4'hF) |-> ##1 (COUNT == 4'h0)
    );

    // If EN=1 and COUNT is 0 (not in reset), next COUNT becomes 1.
    increment_from_zero_when_en: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b1 && COUNT == 4'h0) |-> ##1 (COUNT == 4'h1)
    );

    // If EN=0 and COUNT is 0 (not in reset), next COUNT remains 0.
    hold_zero_when_en0: assert property (
        @(posedge clk) disable iff (!RST) (EN == 1'b0 && COUNT == 4'h0) |-> ##1 (COUNT == 4'h0)
    );
endmodule