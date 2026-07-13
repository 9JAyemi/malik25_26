module top_module_sva (
    input logic CLK,
    input logic RST,
    input logic CLR,
    input logic LD,
    input logic [3:0] DATA,
    input logic [4:0] Q
);

    ///// Combinational output range /////
    // Q is the 5-bit sum of two 4-bit counters; it can never exceed 30.
    check_q_within_valid_range: assert property (
        @(posedge CLK) disable iff (RST) (Q <= 5'd30)
    );

    ///// Reset and clear interactions (synchronous, active-high) /////
    // If both RST and CLR are HIGH in a cycle, Q must be 0 in the next cycle.
    check_both_resets_force_zero_next: assert property (
        @(posedge CLK) (RST && CLR) |=> (Q == 5'd0)
    );

    // If RST is HIGH and CLR is LOW and LD is HIGH, Q loads DATA next cycle.
    check_rst_and_ld_loads_data_next: assert property (
        @(posedge CLK) (RST && !CLR && LD) |=> (Q == $past(DATA))
    );

    // If RST is HIGH and CLR is LOW (LD don't care), Q is in 0..15 next cycle.
    check_rst_without_clr_bounds_next: assert property (
        @(posedge CLK) (RST && !CLR) |=> (Q <= 5'd15)
    );

    // If CLR is HIGH (regardless of LD), Q is in 0..15 next cycle (RST not asserted).
    check_clr_bounds_next: assert property (
        @(posedge CLK) disable iff (RST) (CLR) |=> (Q <= 5'd15)
    );

    // When RST and CLR and LD are all HIGH together, Q still goes to 0 next cycle (CLR priority over LD and RST forces binary_counter to 0).
    check_ld_ignored_when_both_resets: assert property (
        @(posedge CLK) (RST && CLR && LD) |=> (Q == 5'd0)
    );

    ///// Free-running behavior when no controls are asserted /////
    // With no RST/CLR/LD and Q <= 14, both 4-bit counters increment without wrap so Q increases by 2 next cycle.
    check_increment_by_two_when_small: assert property (
        @(posedge CLK) disable iff (RST)
            (!RST && !CLR && !LD && (Q <= 5'd14)) |=> (Q == ($past(Q) + 5'd2))
    );

    // With two consecutive cycles of no RST/CLR/LD and Q <= 13 at the first, Q increases by 4 after two cycles (no wrap in either counter).
    check_two_cycle_increment_when_small: assert property (
        @(posedge CLK) disable iff (RST)
            ((!RST && !CLR && !LD && (Q <= 5'd13)) ##1 (!RST && !CLR && !LD)) |=> (Q == ($past(Q, 2) + 5'd4))
    );

    ///// Persistence under sustained resets /////
    // If both RST and CLR hold HIGH for two consecutive cycles, Q remains 0 one cycle later as well.
    check_zero_persists_while_both_resets_hold: assert property (
        @(posedge CLK) ((RST && CLR) ##1 (RST && CLR)) |=> (Q == 5'd0)
    );

endmodule