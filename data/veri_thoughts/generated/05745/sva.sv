module clk_gated_module_sva (
    input logic src_clk,
    input logic clk_en,
    input logic gated_clk,
    input logic clk_en_reg
);

    // clk_en_reg captures clk_en from the previous src_clk rising edge.
    check_clk_en_reg_captures_clk_en: assert property (
        @(posedge src_clk) 1'b1 |=> (clk_en_reg == $past(clk_en))
    );

    // gated_clk is low just before each src_clk rising edge.
    check_gated_clk_low_before_src_clk_rise: assert property (
        @(posedge src_clk) (gated_clk == 1'b0)
    );

    // gated_clk matches clk_en_reg just before each src_clk falling edge.
    check_gated_clk_matches_clk_en_reg_before_src_clk_fall: assert property (
        @(negedge src_clk) (gated_clk == clk_en_reg)
    );

endmodule