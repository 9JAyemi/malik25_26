module Register_sva (
    input logic [31:0] IN,
    input logic Clk,
    input logic Reset,
    input logic Load,
    input logic [31:0] OUT
);
    // On reset, OUT is cleared on the next cycle.
    check_reset_clears_out_next: assert property (
        @(posedge Clk) Reset |=> (OUT == 32'h0000_0000)
    );

    // Reset overrides Load when both asserted.
    check_reset_overrides_load: assert property (
        @(posedge Clk) (Reset && Load) |=> (OUT == 32'h0000_0000)
    );

    // While reset is held across cycles, OUT remains zero.
    check_out_zero_while_reset_held: assert property (
        @(posedge Clk) (Reset && $past(Reset)) |-> (OUT == 32'h0000_0000)
    );

    // With Load and not Reset, OUT captures IN on the next cycle.
    check_load_updates_out: assert property (
        @(posedge Clk) disable iff (Reset) Load |=> (OUT == $past(IN))
    );

    // When idle (no reset, no load), OUT holds its value.
    check_hold_when_idle: assert property (
        @(posedge Clk) disable iff (Reset) (!Load) |=> (OUT == $past(OUT))
    );

    // Any change to OUT must be caused by prior Reset or Load.
    check_out_change_has_cause: assert property (
        @(posedge Clk) disable iff (Reset) (OUT != $past(OUT)) |-> ($past(Reset) || ($past(Load) && !$past(Reset)))
    );

    // Two consecutive loads update OUT with the second cycle's IN.
    sequence two_consecutive_loads;
        (!Reset && Load) ##1 (!Reset && Load);
    endsequence
    check_two_consecutive_loads: assert property (
        @(posedge Clk) disable iff (Reset) two_consecutive_loads |=> (OUT == $past(IN))
    );

    // Two idle cycles (no reset, no load) keep OUT unchanged across both.
    check_two_idle_cycles_hold: assert property (
        @(posedge Clk) disable iff (Reset) (!Load && !Reset) ##1 (!Load && !Reset) |=> (OUT == $past(OUT,2))
    );
endmodule