module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W55_0_0_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE,
    input logic gated_clk
);

    // Internal gate state sets when enabled with TE high.
    check_gate_state_loads_high: assert property (
        @(posedge CLK) (EN && TE) |=> gated_clk
    );

    // Internal gate state clears when enabled with TE low.
    check_gate_state_loads_low: assert property (
        @(posedge CLK) (EN && !TE) |=> !gated_clk
    );

    // A high gate state is held when enable is low.
    check_gate_state_holds_high_when_disabled: assert property (
        @(posedge CLK) (!EN && gated_clk) |=> gated_clk
    );

    // A low gate state is held when enable is low.
    check_gate_state_holds_low_when_disabled: assert property (
        @(posedge CLK) (!EN && !gated_clk) |=> !gated_clk
    );

    // The gated clock can only rise when the internal gate is open.
    check_enclk_rise_requires_gate_open: assert property (
        @(posedge ENCLK) gated_clk
    );

    // A closed internal gate forces the gated clock low.
    check_gate_closed_forces_enclk_low: assert property (
        @(posedge CLK) !gated_clk |-> !ENCLK
    );

endmodule