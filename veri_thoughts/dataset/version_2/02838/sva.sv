module IORegister_sva #(
    parameter int Width = 32,
    parameter logic [Width-1:0] Initial = {Width{1'bx}},
    parameter bit AsyncReset = 0,
    parameter bit AsyncSet = 0,
    parameter logic [Width-1:0] ResetValue = {Width{1'b0}},
    parameter logic [Width-1:0] SetValue = {Width{1'b1}}
) (
    input logic                 Clock,
    input logic                 Reset,     // Active HIGH
    input logic                 Set,       // Active HIGH
    input logic                 Enable,
    input logic [Width-1:0]     In,
    input logic [Width-1:0]     Out
);

    // Reset loads ResetValue on the next clock edge.
    check_reset_loads_resetvalue_next: assert property (
        @(posedge Clock) Reset |=> (Out === ResetValue)
    );

    // Reset has priority over Set on the next clock edge.
    check_reset_over_set_priority: assert property (
        @(posedge Clock) (Reset && Set) |=> (Out === ResetValue)
    );

    // With synchronous Reset (no async reset), Set loads SetValue on the next clock edge.
    if (!AsyncReset) begin : g_sync_reset_only
        check_set_loads_setvalue_next_syncreset: assert property (
            @(posedge Clock) disable iff (Reset) Set |=> (Out === SetValue)
        );
        // With synchronous Reset, Set has priority over Enable on the next clock edge.
        check_set_over_enable_priority_syncreset: assert property (
            @(posedge Clock) disable iff (Reset) (Set && Enable) |=> (Out === SetValue)
        );
    end

    // Fully synchronous case (no async reset or set): full functional update and hold rules.
    if ((!AsyncReset) && (!AsyncSet)) begin : g_fully_sync
        // Enable captures In on the next clock when Reset and Set are LOW.
        check_enable_loads_input_next_sync: assert property (
            @(posedge Clock) disable iff (Reset) (!Set && Enable) |=> (Out === $past(In))
        );
        // When Reset, Set, and Enable are LOW, Out holds its previous value.
        check_hold_without_ctrl_sync: assert property (
            @(posedge Clock) disable iff (Reset) (!Set && !Enable) |=> (Out === $past(Out))
        );
        // Full next-cycle functional update from previous-cycle controls.
        check_functional_update_sync: assert property (
            @(posedge Clock) disable iff (Reset)
                1'b1 |-> (Out === ($past(Reset) ? ResetValue
                                  : ($past(Set) ? SetValue
                                  : ($past(Enable) ? $past(In) : $past(Out)))))
        );
    end

    // If Reset is held across consecutive clocks, Out is ResetValue.
    check_reset_held_keeps_resetvalue: assert property (
        @(posedge Clock) ($past(Reset) && Reset) |-> (Out === ResetValue)
    );

endmodule