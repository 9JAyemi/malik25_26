module clock_gate_sva (
    input logic clk,
    input logic en,
    input logic enclk
);

    // If en is high on a clock edge, enclk is high on the next clock edge.
    check_en_high_sets_enclk: assert property (
        @(posedge clk) (en === 1'b1) |=> (enclk === 1'b1)
    );

    // If en is low on a clock edge, enclk is low on the next clock edge.
    check_en_low_clears_enclk: assert property (
        @(posedge clk) (en === 1'b0) |=> (enclk === 1'b0)
    );

    // enclk reflects the en value sampled on the previous clock edge.
    check_enclk_tracks_previous_en: assert property (
        @(posedge clk) ((en === 1'b1) || (en === 1'b0)) |=> (enclk === $past(en))
    );

endmodule