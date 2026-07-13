module top_module_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);

    // anyedge matches the RTL equation using the two previous input samples.
    check_anyedge_matches_rtl: assert property (
        @(posedge clk)
        (!$isunknown($past(in,1)) && !$isunknown($past(in,2))) |->
        (anyedge == (($past(in,1) != $past(in,2)) ? 8'h00 : ($past(in,1) & ~$past(in,2))))
    );

    // A sampled input change causes anyedge to be cleared on the following cycle.
    check_change_branch_clears_output: assert property (
        @(posedge clk)
        (!$isunknown($past(in,1)) && !$isunknown($past(in,2)) && ($past(in,1) != $past(in,2))) |->
        (anyedge == 8'h00)
    );

    // When sampled inputs match, anyedge follows the in & ~prev_in branch.
    check_stable_branch_expression: assert property (
        @(posedge clk)
        (!$isunknown($past(in,1)) && !$isunknown($past(in,2)) && ($past(in,1) == $past(in,2))) |->
        (anyedge == ($past(in,1) & ~$past(in,2)))
    );

    // With two known prior samples, the implemented logic always drives anyedge low.
    check_anyedge_always_zero_after_startup: assert property (
        @(posedge clk)
        (!$isunknown($past(in,1)) && !$isunknown($past(in,2))) |->
        (anyedge == 8'h00)
    );

endmodule