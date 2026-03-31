module c_clkgate_sva (
    input logic clk,
    input logic active,
    input logic clk_gated
);

// clk_gated must be low when clk is low.
    check_clk_low_forces_gated_low: assert property (
        @(posedge clk) (clk == 1'b0) |-> (clk_gated == 1'b0)
    );

// clk_gated must be low when active is low.
    check_active_low_forces_gated_low: assert property (
        @(posedge clk) (active == 1'b0) |-> (clk_gated == 1'b0)
    );

// clk_gated must be high when both clk and active are high.
    check_both_high_sets_gated_high: assert property (
        @(posedge clk) (clk == 1'b1 && active == 1'b1) |-> (clk_gated == 1'b1)
    );

// A high clk_gated implies both clk and active are high.
    check_gated_high_requires_both_high: assert property (
        @(posedge clk) (clk_gated == 1'b1) |-> (clk == 1'b1 && active == 1'b1)
    );

// Rising active with clk high must drive clk_gated high.
    check_active_rise_sets_gated_when_clk_high: assert property (
        @(posedge clk) (active == 1'b1 && $rose(active)) |-> (clk_gated == 1'b1)
    );

// Falling active with clk high must drive clk_gated low.
    check_active_fall_clears_gated_when_clk_high: assert property (
        @(posedge clk) (active == 1'b0 && $fell(active)) |-> (clk_gated == 1'b0)
    );

endmodule
