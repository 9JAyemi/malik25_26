module GreaterThan_sva(
    input logic        clk,
    input logic        reset,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic        result
);

    // A reset cycle must drive result low by the next sampled cycle.
    check_reset_clears_result: assert property (
        @(posedge clk)
        reset |=> (result == 1'b0)
    );

    // Outside reset, a prior A>B comparison must set result high.
    check_gt_sets_result: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && ($past(A) > $past(B)) |-> (result == 1'b1)
    );

    // Outside reset, a prior A<=B comparison must clear result low.
    check_le_clears_result: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) && ($past(A) <= $past(B)) |-> (result == 1'b0)
    );

    // Each sampled cycle must reflect the previous cycle's reset or compare result.
    check_registered_compare_behavior: assert property (
        @(posedge clk)
        !$initstate |-> (result == ($past(reset) ? 1'b0 : ($past(A) > $past(B))))
    );

endmodule