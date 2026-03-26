module clock_gating_cell_sva (
    input logic clk,
    input logic enable,
    input logic gated_clk
);

    // Before clk rises, the gated clock must be low.
    check_gated_clk_low_on_posedge: assert property (
        @(posedge clk) gated_clk == 1'b0
    );

    // With enable low, the gated clock must be low before clk falls.
    check_gated_clk_blocked_when_disabled: assert property (
        @(negedge clk) !enable |-> (gated_clk == 1'b0)
    );

    // With enable high, the gated clock must be high before clk falls.
    check_gated_clk_passes_when_enabled: assert property (
        @(negedge clk) enable |-> (gated_clk == 1'b1)
    );

endmodule