module adder_tree_top_sva (
    input logic clk,
    input logic [`ADDER_WIDTH+0-1:0] isum0_0_0_0,
    input logic [`ADDER_WIDTH+0-1:0] isum0_0_0_1,
    input logic [`ADDER_WIDTH+0-1:0] isum0_0_1_0,
    input logic [`ADDER_WIDTH+0-1:0] isum0_0_1_1,
    input logic [`ADDER_WIDTH+0-1:0] isum0_1_0_0,
    input logic [`ADDER_WIDTH+0-1:0] isum0_1_0_1,
    input logic [`ADDER_WIDTH+0-1:0] isum0_1_1_0,
    input logic [`ADDER_WIDTH+0-1:0] isum0_1_1_1,
    input logic [`ADDER_WIDTH:0]     sum
);
    // Clock: clk posedge. No reset in RTL. Sequential pipeline with 1-cycle latency to sum (2_LEVEL_ADDER active).

    // Localparams for safe sizing without relying on macros outside this file.
    localparam int SW = $bits(sum);                  // sum width
    localparam int IW = $bits(isum0_0_0_0);          // input element width

    ///// Functional correctness (2-level tree selected) /////
    // Next-cycle sum equals truncated ((isum0_0_0_0+isum0_0_0_1) + (isum0_0_1_0+isum0_0_1_1)) from this cycle.
    check_sum_matches_two_level_tree: assert property (
        @(posedge clk)
        1'b1 |=> sum == (
            ( {1'b0, ({1'b0, isum0_0_0_0} + {1'b0, isum0_0_0_1})}
            + {1'b0, ({1'b0, isum0_0_1_0} + {1'b0, isum0_0_1_1})} )[SW-1:0]
        )
    );

    // Next-cycle sum equals truncated direct sum of the first four inputs from this cycle.
    check_sum_matches_flat_sum4: assert property (
        @(posedge clk)
        1'b1 |=> sum == (
            ( {2'b00, isum0_0_0_0} + {2'b00, isum0_0_0_1}
            + {2'b00, isum0_0_1_0} + {2'b00, isum0_0_1_1} )[SW-1:0]
        )
    );

    ///// Stability and dependence /////
    // If the first four inputs are stable this cycle, sum is stable next cycle.
    check_sum_stable_when_first4_stable: assert property (
        @(posedge clk)
        $stable({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1}) |=> (sum == $past(sum))
    );

    // If sum changes from last cycle to this cycle, at least one of the first four inputs changed in the prior cycle step.
    check_sum_change_implies_first4_change: assert property (
        @(posedge clk)
        (sum != $past(sum)) |-> ($past({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1}) != $past({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1}, 2))
    );

    // Changes to the unused four inputs alone (with first four stable) do not affect next-cycle sum.
    check_unused_half_no_effect: assert property (
        @(posedge clk)
        $stable({isum0_0_0_0, isum0_0_0_1, isum0_0_1_0, isum0_0_1_1}) && $changed({isum0_1_0_0, isum0_1_0_1, isum0_1_1_0, isum0_1_1_1})
        |=> (sum == $past(sum))
    );

endmodule