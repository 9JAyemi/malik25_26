module ADD32_sva
  (input  logic signed [31:0] S,
   input  logic signed [31:0] A,
   input  logic signed [31:0] B,
   input  logic               C,   // Clock
   input  logic               CE,  // Clock Enable
   input  logic               R    // Synchronous Reset (active-high)
   );

    // Next-state function matches RTL: reset has priority, else CE updates sum, else hold.
    check_next_state_function: assert property (
        @(posedge C) 1'b1 |=> ( S == ( $past(R) ? 32'sd0 : ($past(CE) ? ($past(A) + $past(B)) : $past(S)) ) )
    );

    // On any cycle with reset asserted, S becomes 0 on the next cycle.
    check_sync_reset_clears_S: assert property (
        @(posedge C) R |=> (S == 32'sd0)
    );

    // With CE high and not in reset, S updates to A+B on the next cycle.
    check_update_when_CE_high: assert property (
        @(posedge C) disable iff (R) CE |=> (S == $past(A) + $past(B))
    );

    // With CE low and not in reset, S holds its previous value on the next cycle.
    check_hold_when_CE_low: assert property (
        @(posedge C) disable iff (R) !CE |=> (S == $past(S))
    );

    // Reset has priority over CE when both are asserted.
    check_reset_priority_over_CE: assert property (
        @(posedge C) (R && CE) |=> (S == 32'sd0)
    );

    // If CE is high and A+B is zero (not in reset), next S is zero.
    check_sum_zero_case: assert property (
        @(posedge C) disable iff (R) (CE && ((A + B) == 32'sd0)) |=> (S == 32'sd0)
    );

    // If CE is high and A+B equals current S (not in reset), S remains unchanged next cycle.
    check_idempotent_update_when_sum_equals_S: assert property (
        @(posedge C) disable iff (R) (CE && ((A + B) == S)) |=> (S == $past(S))
    );

    // If CE stays low for two consecutive cycles (not in reset), S is unchanged across them.
    check_hold_two_cycles_when_CE_low: assert property (
        @(posedge C) disable iff (R) (!CE ##1 !CE) |-> (S == $past(S))
    );

endmodule