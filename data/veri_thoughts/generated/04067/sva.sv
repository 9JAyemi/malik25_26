module HardRegister_sva #(
    parameter int Width = 32,
    parameter bit AsyncReset = 0,
    parameter bit AsyncSet = 0,
    parameter logic [Width-1:0] ResetValue = {Width{1'b0}},
    parameter logic [Width-1:0] SetValue = {Width{1'b1}}
) (
    input logic Clock,
    input logic Reset,
    input logic Set,
    input logic Enable,
    input logic [Width-1:0] In,
    input logic [Width-1:0] Out
);

    // Clock is posedge Clock.
    // Reset is active-high; async behavior depends on AsyncReset/AsyncSet.

    generate
        if (!AsyncReset && !AsyncSet) begin : gen_sync_reset_sync_set
            // A sampled reset cycle forces ResetValue on the next observed cycle.
            check_sync_reset_value: assert property (
                @(posedge Clock) disable iff (Reset)
                $past(Reset) |-> (Out == ResetValue)
            );

            // Set has priority over Enable when reset was not active.
            check_sync_set_value: assert property (
                @(posedge Clock) disable iff (Reset)
                (!$past(Reset) && $past(Set)) |-> (Out == SetValue)
            );

            // Enable captures In when neither reset nor set was active.
            check_sync_enable_capture: assert property (
                @(posedge Clock) disable iff (Reset)
                (!$past(Reset) && !$past(Set) && $past(Enable)) |-> (Out == $past(In))
            );

            // The register holds its value when no control was active.
            check_sync_hold_value: assert property (
                @(posedge Clock) disable iff (Reset)
                (!$past(Reset) && !$past(Set) && !$past(Enable)) |-> (Out == $past(Out))
            );
        end else if (AsyncReset && !AsyncSet) begin : gen_async_reset_sync_set
            // While async reset is high, Out must already be ResetValue.
            check_async_reset_level_value: assert property (
                @(posedge Clock) disable iff (1'b0)
                Reset |-> (Out == ResetValue)
            );

            // After a sampled reset cycle, Out remains at ResetValue until a later clocked update.
            check_async_reset_release_value: assert property (
                @(posedge Clock) disable iff (Reset)
                $past(Reset) |-> (Out == ResetValue)
            );
        end else if (!AsyncReset && AsyncSet) begin : gen_sync_reset_async_set
            // No robust clocked-only assertion is emitted for this mixed async-set configuration.
        end else begin : gen_async_reset_async_set
            // While async reset is high, Out must already be ResetValue.
            check_async_reset_level_value_with_async_set: assert property (
                @(posedge Clock) disable iff (1'b0)
                Reset |-> (Out == ResetValue)
            );
        end
    endgenerate

endmodule