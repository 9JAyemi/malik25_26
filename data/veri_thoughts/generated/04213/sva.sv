module SNPS_CLOCK_GATE_HIGH_counter_d_W4_77_sva (
    input logic       CLK,
    input logic       EN,
    input logic       TE,
    input logic       ENCLK,
    input logic [3:0] count,
    input logic [3:0] next_count
);

    // next_count is always count plus one.
    check_next_count_relation: assert property (
        @(posedge CLK) next_count == (count + 4'd1)
    );

    // ENCLK always reflects the MSB of count.
    check_enclk_matches_count_msb: assert property (
        @(posedge CLK) ENCLK == count[3]
    );

    // When enabled and TE is low, count increments if not at 4'hF.
    check_count_increments_when_enabled: assert property (
        @(posedge CLK) (EN && !TE && (count != 4'hF)) |=> (count == ($past(count) + 4'd1))
    );

    // When enabled and TE is low at 4'hF, count wraps to zero.
    check_count_wraps_at_max: assert property (
        @(posedge CLK) (EN && !TE && (count == 4'hF)) |=> (count == 4'h0)
    );

    // When EN is low, count holds its value.
    check_count_holds_when_en_low: assert property (
        @(posedge CLK) (!EN) |=> (count == $past(count))
    );

    // When TE is high while EN is high, counting is blocked.
    check_te_blocks_counting: assert property (
        @(posedge CLK) (EN && TE) |=> (count == $past(count))
    );

endmodule