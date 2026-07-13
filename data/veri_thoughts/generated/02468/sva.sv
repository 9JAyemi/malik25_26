module counter_adder_module_sva (
    input logic clk,
    input logic reset,      // active-high synchronous reset
    input logic select,
    input logic [3:0] out
);
    ///// Reset behavior /////
    // If reset is asserted, out becomes 0 on the next clock.
    reset_next_cycle_zero: assert property (
        @(posedge clk) reset |=> (out == 4'd0)
    );

    // While reset stays asserted across consecutive cycles, out is 0.
    reset_hold_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (out == 4'd0)
    );

    // Immediately after reset deasserts, out is 0 (loaded by prior reset cycle).
    reset_deassert_out_zero: assert property (
        @(posedge clk) $past(reset) && !reset |-> (out == 4'd0)
    );

    ///// Output step behavior vs. select history (two-cycle lookahead) /////
    // If select stays 0 for two consecutive cycles, out increments by 1 in the next cycle.
    step_when_select00_next: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(select) == 1'b0) && (select == 1'b0))
        |-> ##1 (out == $past(out) + 4'd1)
    );

    // If select stays 1 for two consecutive cycles, out increments by 1 in the next cycle.
    step_when_select11_next: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(select) == 1'b1) && (select == 1'b1))
        |-> ##1 (out == $past(out) + 4'd1)
    );

    // If select toggles 0->1, out increments by 2 in the next cycle.
    step_when_select01_next: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(select) == 1'b0) && (select == 1'b1))
        |-> ##1 (out == $past(out) + 4'd2)
    );

    // If select toggles 1->0, out holds its value in the next cycle.
    hold_when_select10_next: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(select) == 1'b1) && (select == 1'b0))
        |-> ##1 (out == $past(out))
    );

    // If select is X/Z in a cycle, no case item matches and out holds next cycle.
    hold_when_select_unknown_next: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && (select !== 1'b0) && (select !== 1'b1))
        |-> ##1 (out == $past(out))
    );

    ///// Immediate (one-cycle) output step vs. prior select pair /////
    // If prior two selects were equal, out increments by 1 this cycle.
    step_now_when_prev_equal: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1) && !$past(reset,2) && ($past(select,1) == $past(select,2)))
        |-> (out == $past(out) + 4'd1)
    );

    // If prior selects were 0 then 1, out increments by 2 this cycle.
    step_now_when_prev01: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1) && !$past(reset,2) && ($past(select,1) == 1'b1) && ($past(select,2) == 1'b0))
        |-> (out == $past(out) + 4'd2)
    );

    // If prior selects were 1 then 0, out holds this cycle.
    hold_now_when_prev10: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset,1) && !$past(reset,2) && ($past(select,1) == 1'b0) && ($past(select,2) == 1'b1))
        |-> (out == $past(out))
    );
endmodule