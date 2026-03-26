module clock_gating_cell_sva (
    input logic clk,
    input logic en,
    input logic gated_clk
);

    // Before clk rises, clk is low so the output must be high.
    check_gated_clk_high_before_clk_rise: assert property (
        @(posedge clk) (gated_clk == 1'b1)
    );

    // Before clk falls, a low enable keeps the output high.
    check_gated_clk_high_when_clk_high_and_en_low: assert property (
        @(negedge clk) (!en) |-> (gated_clk == 1'b1)
    );

    // Before clk falls, a high enable drives the output low.
    check_gated_clk_low_when_clk_high_and_en_high: assert property (
        @(negedge clk) en |-> (gated_clk == 1'b0)
    );

endmodule