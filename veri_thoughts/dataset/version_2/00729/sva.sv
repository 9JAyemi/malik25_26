module add8_sva (
    input logic clk,           // Sampling clock for assertions (DUT is combinational)
    input logic [7:0] X,
    input logic [7:0] Y,
    input logic [7:0] S,
    input logic Cout
);
    // Purely combinational DUT (no clock/reset); assertions are sampled on clk.
    // 8-bit ripple add built from two 4-bit adders; lower-nibble adder Cin is unconnected (environment unconstrained).

    ///// Combinational determinism /////
    // If inputs hold their values, outputs must hold (stateless combinational mapping).
    check_outputs_hold_when_inputs_hold: assert property (
        @(posedge clk) $stable({X, Y}) |-> $stable({S, Cout})
    );

    // Outputs cannot change unless at least one input bit changed.
    check_outputs_change_implies_inputs_change: assert property (
        @(posedge clk) $changed({S, Cout}) |-> $changed({X, Y})
    );

    // Sum bus change implies some input changed.
    check_sum_change_implies_inputs_change: assert property (
        @(posedge clk) $changed(S) |-> $changed({X, Y})
    );

    // Carry-out change implies some input changed.
    check_cout_change_implies_inputs_change: assert property (
        @(posedge clk) $changed(Cout) |-> $changed({X, Y})
    );

    ///// Structural independence /////
    // Lower-nibble sum does not depend on upper-nibble inputs; if low inputs hold, low sum holds.
    check_lower_nibble_stable_when_low_inputs_hold: assert property (
        @(posedge clk) $stable({X[3:0], Y[3:0]}) |-> $stable(S[3:0])
    );

    // Changing only upper-nibble inputs cannot affect the lower-nibble sum.
    check_lower_nibble_immune_to_upper_changes: assert property (
        @(posedge clk) ($stable({X[3:0], Y[3:0]}) && $changed({X[7:4], Y[7:4]})) |-> $stable(S[3:0])
    );

endmodule