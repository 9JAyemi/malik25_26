module IORegister_sva #(
    parameter int Width = 32,
    parameter logic [Width-1:0] Initial = {Width{1'bx}},
    parameter bit AsyncReset = 1'b0,
    parameter bit AsyncSet = 1'b0,
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

generate
    if (AsyncReset && !AsyncSet) begin : gen_reset_only
        // Reset loads ResetValue on the next clock.
        check_reset_only_reset_value: assert property (
            @(posedge Clock) disable iff (1'b0) Reset |=> (Out === ResetValue)
        );

        // Enable loads In when reset is not asserted.
        check_reset_only_capture_input: assert property (
            @(posedge Clock) disable iff (Reset) Enable |=> (Out === $past(In))
        );

        // Without reset or enable, the register holds its value.
        check_reset_only_hold_value: assert property (
            @(posedge Clock) disable iff (Reset) !Enable |=> (Out === $past(Out))
        );
    end else if (!AsyncReset && AsyncSet) begin : gen_set_only
        // Set loads SetValue on the next clock.
        check_set_only_set_value: assert property (
            @(posedge Clock) disable iff (1'b0) Set |=> (Out === SetValue)
        );

        // Enable loads In when set is not asserted.
        check_set_only_capture_input: assert property (
            @(posedge Clock) disable iff (1'b0) (!Set && Enable) |=> (Out === $past(In))
        );

        // Without set or enable, the register holds its value.
        check_set_only_hold_value: assert property (
            @(posedge Clock) disable iff (1'b0) (!Set && !Enable) |=> (Out === $past(Out))
        );
    end else begin : gen_reset_set
        // Reset has highest priority and loads ResetValue.
        check_reset_set_reset_value: assert property (
            @(posedge Clock) disable iff (1'b0) Reset |=> (Out === ResetValue)
        );

        // Set loads SetValue when reset is not asserted.
        check_reset_set_set_value: assert property (
            @(posedge Clock) disable iff (Reset) Set |=> (Out === SetValue)
        );

        // Enable loads In when reset and set are not asserted.
        check_reset_set_capture_input: assert property (
            @(posedge Clock) disable iff (Reset) (!Set && Enable) |=> (Out === $past(In))
        );

        // Without reset, set, or enable, the register holds its value.
        check_reset_set_hold_value: assert property (
            @(posedge Clock) disable iff (Reset) (!Set && !Enable) |=> (Out === $past(Out))
        );
    end
endgenerate

endmodule