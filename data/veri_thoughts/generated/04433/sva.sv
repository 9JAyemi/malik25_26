module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in,
    input logic anyedge,
    input logic [7:0] swapped_in,
    input logic edge_detected
);

    // Byte swap leaves the sampled byte unchanged.
    check_swapped_in_matches_in: assert property (
        @(posedge clk) disable iff (reset)
        (swapped_in === in)
    );

    // A change on swapped_in between the two previous samples sets current edge_detected.
    check_edge_detected_after_change: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(swapped_in)) &&
         !$isunknown($past(swapped_in, 2)) &&
         ($past(swapped_in) != $past(swapped_in, 2))) |-> (edge_detected == 1'b1)
    );

    // No change on swapped_in between the two previous samples clears current edge_detected.
    check_edge_detected_after_stable: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(swapped_in)) &&
         !$isunknown($past(swapped_in, 2)) &&
         ($past(swapped_in) == $past(swapped_in, 2))) |-> (edge_detected == 1'b0)
    );

    // Reset on the previous clock forces current anyedge low.
    check_anyedge_low_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(reset)) && $past(reset)) |-> (anyedge == 1'b0)
    );

    // Previous high edge_detected propagates to current anyedge when reset was low.
    check_anyedge_after_edge_detected_high: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(reset)) &&
         !$past(reset) &&
         !$isunknown($past(edge_detected)) &&
         $past(edge_detected)) |-> (anyedge == 1'b1)
    );

    // Previous low edge_detected propagates to current anyedge when reset was low.
    check_anyedge_after_edge_detected_low: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(reset)) &&
         !$past(reset) &&
         !$isunknown($past(edge_detected)) &&
         !$past(edge_detected)) |-> (anyedge == 1'b0)
    );

    // An input change two cycles ago sets current anyedge when the previous cycle was not reset.
    check_anyedge_after_input_change: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(reset)) &&
         !$past(reset) &&
         !$isunknown($past(in, 2)) &&
         !$isunknown($past(in, 3)) &&
         ($past(in, 2) != $past(in, 3))) |-> (anyedge == 1'b1)
    );

    // Input stability two cycles ago clears current anyedge when the previous cycle was not reset.
    check_anyedge_after_input_stable: assert property (
        @(posedge clk) disable iff (reset)
        (!$isunknown($past(reset)) &&
         !$past(reset) &&
         !$isunknown($past(in, 2)) &&
         !$isunknown($past(in, 3)) &&
         ($past(in, 2) == $past(in, 3))) |-> (anyedge == 1'b0)
    );

    // A reset asserted on this clock drives anyedge low by the next sampled cycle.
    check_reset_clears_anyedge: assert property (
        @(posedge clk)
        reset |=> (anyedge == 1'b0)
    );

endmodule