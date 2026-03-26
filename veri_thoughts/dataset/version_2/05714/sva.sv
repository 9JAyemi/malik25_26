module Register_sva #(
    parameter               Width = 32,
                            Initial = {Width{1'bx}},
                            AsyncReset = 0,
                            AsyncSet = 0,
                            ResetValue = {Width{1'b0}},
                            SetValue = {Width{1'b1}}
) (
    input  logic             Clock,
    input  logic             Reset,
    input  logic             Set,
    input  logic             Enable,
    input  logic [Width-1:0] In,
    input  logic [Width-1:0] Out
);

generate
    if (!AsyncReset && !AsyncSet) begin : g_sync_sync
        // Reset loads ResetValue on the next sampled cycle.
        check_reset_value: assert property (
            @(posedge Clock) !$initstate && $past(Reset) |-> Out == ResetValue
        );

        // Set loads SetValue when reset was low.
        check_set_value: assert property (
            @(posedge Clock) disable iff (Reset)
            !$initstate && $past(!Reset && Set) |-> Out == SetValue
        );

        // Enable loads In when reset and set were low.
        check_enable_load: assert property (
            @(posedge Clock) disable iff (Reset)
            !$initstate && $past(!Reset && !Set && Enable) |-> Out == $past(In)
        );

        // Out holds its value when no control was active.
        check_hold_value: assert property (
            @(posedge Clock) disable iff (Reset)
            !$initstate && $past(!Reset && !Set && !Enable) |-> Out == $past(Out)
        );

        // Reset has priority over set.
        check_reset_over_set: assert property (
            @(posedge Clock) !$initstate && $past(Reset && Set) |-> Out == ResetValue
        );

    end else if (AsyncReset && !AsyncSet) begin : g_async_reset_sync_set
        // Any sampled reset leaves Out at ResetValue.
        check_async_reset_value: assert property (
            @(posedge Clock) !$initstate && $past(Reset) |-> Out == ResetValue
        );

    end else if (!AsyncReset && AsyncSet) begin : g_sync_reset_async_set
        // A sampled set request leaves Out at SetValue.
        check_async_set_value: assert property (
            @(posedge Clock) disable iff (Reset)
            !$initstate && $past(!Reset && Set) |-> Out == SetValue
        );

        // Set has priority over enable when reset was low.
        check_async_set_over_enable: assert property (
            @(posedge Clock) disable iff (Reset)
            !$initstate && $past(!Reset && Set && Enable) |-> Out == SetValue
        );

    end else begin : g_async_reset_async_set
        // Continuous reset keeps Out at ResetValue.
        check_async_controls_reset_holds_value: assert property (
            @(posedge Clock) !$initstate && Reset && $past(Reset) |-> Out == ResetValue
        );

        // Reset dominates set while both stay asserted.
        check_async_controls_reset_over_set: assert property (
            @(posedge Clock) !$initstate && Reset && Set && $past(Reset && Set) |-> Out == ResetValue
        );
    end
endgenerate

endmodule