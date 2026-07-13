module dff_with_reset_set_sva (
    input logic D,
    input logic RESET_B,
    input logic SET,
    input logic CLK,
    input logic Q
);

    // Active-low reset forces Q low whenever reset is sampled low.
    check_reset_forces_q_low: assert property (
        @(posedge CLK) !RESET_B |-> (Q == 1'b0)
    );

    // A clock edge taken during reset leaves Q low at the next clock sample.
    check_reset_cycle_clears_q: assert property (
        @(posedge CLK) !RESET_B |=> (Q == 1'b0)
    );

    // On a sampled reset release, Q is still low before the release-cycle update.
    check_reset_release_starts_from_zero: assert property (
        @(posedge CLK) disable iff (!RESET_B) $rose(RESET_B) |-> (Q == 1'b0)
    );

    // Reset has priority over SET when both are asserted together.
    check_reset_priority_over_set: assert property (
        @(posedge CLK) (!RESET_B && SET) |-> (Q == 1'b0)
    );

endmodule