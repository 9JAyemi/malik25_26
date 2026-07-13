module clk_gated_module_sva (
    input logic src_clk,
    input logic clk_en,
    input logic gated_clk
);

// Gated clock is low when the prior-cycle enable was low.
    check_gated_low_when_prev_en_low: assert property (
        @(posedge src_clk) !clk_en |-> !gated_clk
    );

// Gated clock is high when the prior-cycle enable was high.
    check_gated_high_when_prev_en_high: assert property (
        @(posedge src_clk) clk_en |-> gated_clk
    );

// A high gated clock implies the prior-cycle enable was high.
    check_prev_en_high_when_gated_high: assert property (
        @(posedge src_clk) gated_clk |-> clk_en
    );

// A low gated clock implies the prior-cycle enable was low.
    check_prev_en_low_when_gated_low: assert property (
        @(posedge src_clk) !gated_clk |-> !clk_en
    );

endmodule
