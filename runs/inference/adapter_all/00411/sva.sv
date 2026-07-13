module lfsr_counter_sva #(
    parameter SIZE = 4
)(
    input logic clk,
    input logic reset,
    input logic ena,
    input logic [SIZE-1:0] out
);

    // Reset forces the counter output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) !reset |-> (out == '0)
    );

    // When enabled, the counter updates with the registered next state.
    check_enabled_state_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out == $past({out[SIZE-2:0], out[SIZE-1] ^ out[SIZE-2]}))
    );

    // When disabled, the counter holds its previous value.
    check_disabled_state_hold: assert property (
        @(posedge clk) disable iff (!reset)
        !ena |=> (out == $past(out))
    );

    // The upper bits shift from the lower bits when enabled.
    check_shifted_upper_bits: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[SIZE-1:1] == $past(out[SIZE-2:0]))
    );

    // The LSB is the XOR of the previous upper bit and the previous second bit.
    check_lsb_xor_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[0] == $past(out[SIZE-2] ^ out[SIZE-3]))
    );

    // A zero state remains zero on the next cycle when enabled.
    check_zero_state_stays_zero: assert property (
        @(posedge clk) disable iff (!reset)
        (ena && (out == '0)) |=> (out == '0)
    );

    // A zero state remains zero on the next cycle when disabled.
    check_zero_state_holds_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        (!ena && (out == '0)) |=> (out == '0)
    );

endmodule