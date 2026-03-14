module PHASE_ALIGN_sva (
    input logic ENA_COMMA_ALIGN,
    input logic RX_REC_CLK,
    input logic ENA_CALIGN_REC
);
    // Clock: RX_REC_CLK. Reset: none in RTL. Behavior: 2-flop pipeline with 1-cycle output delay.

    // Output equals input delayed by one RX_REC_CLK cycle.
    check_output_one_cycle_delay: assert property (
        @(posedge RX_REC_CLK) 1 |=> (ENA_CALIGN_REC == $past(ENA_COMMA_ALIGN))
    );

    // If input is 1 at cycle N, output must be 1 at cycle N+1.
    check_level_high_propagation: assert property (
        @(posedge RX_REC_CLK) ENA_COMMA_ALIGN |=> ENA_CALIGN_REC
    );

    // If input is 0 at cycle N, output must be 0 at cycle N+1.
    check_level_low_propagation: assert property (
        @(posedge RX_REC_CLK) !ENA_COMMA_ALIGN |=> !ENA_CALIGN_REC
    );

    // A rising edge on input at N causes a rising edge on output at N+1.
    check_rise_propagation: assert property (
        @(posedge RX_REC_CLK) $rose(ENA_COMMA_ALIGN) |=> $rose(ENA_CALIGN_REC)
    );

    // A falling edge on input at N causes a falling edge on output at N+1.
    check_fall_propagation: assert property (
        @(posedge RX_REC_CLK) $fell(ENA_COMMA_ALIGN) |=> $fell(ENA_CALIGN_REC)
    );

    // If input does not change at N, output does not change at N+1.
    check_stability_propagation: assert property (
        @(posedge RX_REC_CLK) !$changed(ENA_COMMA_ALIGN) |=> !$changed(ENA_CALIGN_REC)
    );
endmodule