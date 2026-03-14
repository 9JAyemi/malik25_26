module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W13_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    ///// Synchronous clock gate behavior (no reset present) /////
    // If EN and TE are both HIGH, next-cycle ENCLK must be 0.
    check_next_low_when_EN_and_TE: assert property (
        @(posedge CLK) (EN && TE) |=> (ENCLK == 1'b0)
    );

    // If EN and TE are not both HIGH, next-cycle ENCLK must be 1.
    check_next_high_when_not_both_high: assert property (
        @(posedge CLK) !(EN && TE) |=> (ENCLK == 1'b1)
    );

    // If EN is LOW, next-cycle ENCLK must be 1.
    check_next_high_when_EN_low: assert property (
        @(posedge CLK) (EN == 1'b0) |=> (ENCLK == 1'b1)
    );

    // If TE is LOW, next-cycle ENCLK must be 1.
    check_next_high_when_TE_low: assert property (
        @(posedge CLK) (TE == 1'b0) |=> (ENCLK == 1'b1)
    );

    // Next-cycle ENCLK equals logical NOT of (EN AND TE).
    check_functional_next_value: assert property (
        @(posedge CLK) 1'b1 |=> (ENCLK == ~(EN && TE))
    );

    // If EN and TE stay HIGH for two cycles, ENCLK remains 0 on the following cycle.
    check_persistent_low_when_both_high: assert property (
        @(posedge CLK) (EN && TE) ##1 (EN && TE) |=> (ENCLK == 1'b0)
    );

    // If either EN or TE is LOW for two cycles, ENCLK remains 1 on the following cycle.
    check_persistent_high_when_not_both_high: assert property (
        @(posedge CLK) (!(EN && TE)) ##1 (!(EN && TE)) |=> (ENCLK == 1'b1)
    );
endmodule