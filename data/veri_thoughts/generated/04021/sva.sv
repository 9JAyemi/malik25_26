module ClkDiv_5Hz_sva #(
    parameter [23:0] cntEndVal = 24'h989680
) (
    input logic        CLK,
    input logic        RST,
    input logic        CLKOUT,
    input logic [23:0] clkCount
);

    // Reset clears the divided clock and the counter.
    check_reset_clears_state: assert property (
        @(posedge CLK)
        RST |-> (CLKOUT == 1'b0) && (clkCount == 24'h000000)
    );

    // The counter never exceeds its terminal count.
    check_count_within_range: assert property (
        @(posedge CLK) disable iff (RST)
        clkCount <= cntEndVal
    );

    // Before terminal count, the counter advances by one or is asynchronously reset.
    check_nonterminal_count_advances_or_resets: assert property (
        @(posedge CLK) disable iff (RST)
        (clkCount < cntEndVal) |=> ((clkCount == ($past(clkCount) + 24'h000001)) || (clkCount == 24'h000000))
    );

    // Before terminal count, the output holds its value or is asynchronously reset low.
    check_nonterminal_output_holds_or_resets_low: assert property (
        @(posedge CLK) disable iff (RST)
        (clkCount < cntEndVal) |=> ((CLKOUT == $past(CLKOUT)) || (CLKOUT == 1'b0))
    );

    // At terminal count, the counter wraps back to zero.
    check_terminal_count_wraps_to_zero: assert property (
        @(posedge CLK) disable iff (RST)
        (clkCount == cntEndVal) |=> (clkCount == 24'h000000)
    );

    // At terminal count, the output toggles or is asynchronously reset low.
    check_terminal_output_toggles_or_resets_low: assert property (
        @(posedge CLK) disable iff (RST)
        (clkCount == cntEndVal) |=> ((CLKOUT == ~$past(CLKOUT)) || (CLKOUT == 1'b0))
    );

    // On sampled reset deassertion, state is still the cleared reset state.
    check_reset_release_state_cleared: assert property (
        @(posedge CLK) disable iff (RST)
        $fell(RST) |-> (CLKOUT == 1'b0) && (clkCount == 24'h000000)
    );

    // One cycle after reset release, counting starts or reset has re-cleared state.
    check_first_cycle_after_reset_release: assert property (
        @(posedge CLK) disable iff (RST)
        $fell(RST) |=> (CLKOUT == 1'b0) && ((clkCount == 24'h000001) || (clkCount == 24'h000000))
    );

endmodule

bind ClkDiv_5Hz ClkDiv_5Hz_sva #(.cntEndVal(cntEndVal)) u_ClkDiv_5Hz_sva (
    .CLK(CLK),
    .RST(RST),
    .CLKOUT(CLKOUT),
    .clkCount(clkCount)
);