module register_sva (
    input logic CLK,
    input logic SET,
    input logic RESET,
    input logic [3:0] D,
    input logic [3:0] Q
);
    // Clk: CLK (posedge). RESET is synchronous, active-HIGH. Logic is sequential (flop with conditional load).

    ///// Functional behavior /////
    // Only SET asserted (no RESET): Q loads 4'hF on next cycle.
    set_only_loads_ones: assert property (
        @(posedge CLK) disable iff (RESET) (SET && !RESET) |=> (Q == 4'hF)
    );

    // Only RESET asserted (no SET): Q loads 4'h0 on next cycle.
    reset_only_loads_zeros: assert property (
        @(posedge CLK) (RESET && !SET) |=> (Q == 4'h0)
    );

    // Both deasserted: Q loads D on next cycle.
    both_low_loads_d: assert property (
        @(posedge CLK) disable iff (RESET) (!SET && !RESET) |=> (Q == D)
    );

    // Both asserted: Q loads D on next cycle.
    both_high_loads_d: assert property (
        @(posedge CLK) (SET && RESET) |=> (Q == D)
    );

    // Rising SET with RESET low: Q loads 4'hF on next cycle.
    set_rise_loads_ones: assert property (
        @(posedge CLK) disable iff (RESET) ($rose(SET) && !RESET) |=> (Q == 4'hF)
    );

    // Rising RESET with SET low: Q loads 4'h0 on next cycle.
    reset_rise_loads_zeros: assert property (
        @(posedge CLK) ($rose(RESET) && !SET) |=> (Q == 4'h0)
    );

endmodule