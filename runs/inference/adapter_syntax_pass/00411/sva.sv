module lfsr_counter_sva #(
    parameter SIZE = 4
)(
    input logic clk,
    input logic reset,
    input logic ena,
    input logic [SIZE-1:0] out
);

    // Reset clears the counter on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) !reset |=> (out == {SIZE{1'b0}})
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset) !ena |=> (out == $past(out))
    );

    // When enabled, the counter updates with the implemented feedback.
    check_update_when_enabled: assert property (
        @(posedge clk) disable iff (!reset) ena |=> (out == { $past(out[SIZE-2:0]), ($past(out[SIZE-1]) ^ $past(out[SIZE-2])) })
    );

    // When enabled, the LSB is the XOR of the previous two MSBs.
    check_lsb_update: assert property (
        @(posedge clk) disable iff (!reset) ena |=> (out[0] == ($past(out[SIZE-1]) ^ $past(out[SIZE-2])))
    );

    // When enabled, the upper bits shift down by one.
    check_upper_bits_shift: assert property (
        @(posedge clk) disable iff (!reset) ena |=> (out[SIZE-1:1] == $past(out[SIZE-2:0]))
    );

endmodule