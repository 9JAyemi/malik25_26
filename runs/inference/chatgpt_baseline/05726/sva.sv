module binary_counter_sva #(
    parameter MAX_VALUE = 16
) (
    input logic       CLK,
    input logic       CLR_B,
    input logic       LOAD,
    input logic [4:0] DATA_IN,
    input logic [4:0] Q
);

    localparam logic [4:0] WRAP_VALUE = MAX_VALUE - 1;

    // Clock: CLK. Clear: CLR_B is active high and synchronous.
    // Q clears to zero, loads DATA_IN, wraps at MAX_VALUE-1, otherwise increments.

    // Synchronous clear drives Q to zero.
    check_sync_clear: assert property (
        @(posedge CLK) CLR_B |=> (Q == 5'd0)
    );

    // Clear has priority over load when both are asserted.
    check_clear_priority_over_load: assert property (
        @(posedge CLK) (CLR_B && LOAD) |=> (Q == 5'd0)
    );

    // Load copies DATA_IN into Q when clear is not asserted.
    check_load_copies_data: assert property (
        @(posedge CLK) disable iff (CLR_B)
        (!CLR_B && LOAD) |=> (Q == $past(DATA_IN))
    );

    // Load takes priority over wrap when Q is at the wrap value.
    check_load_priority_over_wrap: assert property (
        @(posedge CLK) disable iff (CLR_B)
        (!CLR_B && LOAD && (Q == WRAP_VALUE)) |=> (Q == $past(DATA_IN))
    );

    // The counter wraps to zero when Q reaches MAX_VALUE-1.
    check_wrap_at_max_minus_one: assert property (
        @(posedge CLK) disable iff (CLR_B)
        (!CLR_B && !LOAD && (Q == WRAP_VALUE)) |=> (Q == 5'd0)
    );

    // The counter increments by one when not clearing, loading, or wrapping.
    check_increment_otherwise: assert property (
        @(posedge CLK) disable iff (CLR_B)
        (!CLR_B && !LOAD && (Q != WRAP_VALUE)) |=> (Q == ($past(Q) + 5'd1))
    );

endmodule