module clk_gated_module_sva (
    input logic src_clk,
    input logic clk_en,
    input logic gated_clk
);

    // gated_clk is high on the first clock after clk_en is high.
    check_gated_clk_high_after_en: assert property (
        @(posedge src_clk) clk_en |=> gated_clk
    );

    // gated_clk is low on the first clock after clk_en is low.
    check_gated_clk_low_after_en_low: assert property (
        @(posedge src_clk) !clk_en |=> !gated_clk
    );

    // gated_clk is high on the second clock after clk_en is high.
    check_gated_clk_high_after_en_two_cycles: assert property (
        @(posedge src_clk) clk_en |=> ##1 gated_clk
    );

    // gated_clk is low on the second clock after clk_en is low.
    check_gated_clk_low_after_en_low_two_cycles: assert property (
        @(posedge src_clk) !clk_en |=> ##1 !gated_clk
    );

endmodule