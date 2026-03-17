module clock_gate_assertions (
    input logic clk,
    input logic en,
    input logic te,
    input logic enclk
);

    // enclk must equal the previous cycle's en && te value.
    check_enclk_matches_previous_inputs: assert property (
        @(posedge clk) !$initstate |-> (enclk == ($past(en) && $past(te)))
    );

    // If both en and te are high, enclk must be high on the next clock.
    check_enclk_sets_after_en_and_te_high: assert property (
        @(posedge clk) (en && te) |=> enclk
    );

    // If en is low, enclk must be low on the next clock.
    check_enclk_clears_after_en_low: assert property (
        @(posedge clk) !en |=> !enclk
    );

    // If te is low, enclk must be low on the next clock.
    check_enclk_clears_after_te_low: assert property (
        @(posedge clk) !te |=> !enclk
    );

endmodule