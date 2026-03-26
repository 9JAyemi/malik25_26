module clock_gate_sva (
    input logic clk,
    input logic enable,
    input logic clk_gated
);

    // clk_gated reflects the previous cycle's enable value.
    check_clk_gated_tracks_previous_enable: assert property (
        @(posedge clk) 1'b1 |=> (clk_gated == $past(enable))
    );

    // A high enable drives clk_gated high on the next sampled cycle.
    check_enable_high_sets_clk_gated: assert property (
        @(posedge clk) enable |=> (clk_gated == 1'b1)
    );

    // A low enable drives clk_gated low on the next sampled cycle.
    check_enable_low_clears_clk_gated: assert property (
        @(posedge clk) !enable |=> (clk_gated == 1'b0)
    );

endmodule