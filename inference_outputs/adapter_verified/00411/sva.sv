module lfsr_counter_sva (
    input logic clk,
    input logic reset,
    input logic ena,
    input logic [3:0] out
);

// Reset drives the counter to zero.
    check_reset_clears_state: assert property (
        @(posedge clk) !reset |-> (out == 4'b0000)
    );

// When enabled, the counter updates with the next LFSR value.
    check_enabled_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out == {$past(out[2:0]), $past(out[3]) ^ $past(out[2])})
    );

// When disabled, the counter holds its value.
    check_disabled_hold: assert property (
        @(posedge clk) disable iff (!reset)
        !ena |=> (out == $past(out))
    );

// Bit 0 shifts in the previous value of bit 2.
    check_bit0_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[0] == $past(out[2]))
    );

// Bit 1 shifts in the previous value of bit 3.
    check_bit1_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[1] == $past(out[3]))
    );

// Bit 2 shifts in the previous value of bit 1.
    check_bit2_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[2] == $past(out[1]))
    );

// Bit 3 is the previous XOR of bits 3 and 2.
    check_bit3_update: assert property (
        @(posedge clk) disable iff (!reset)
        ena |=> (out[3] == $past(out[3]) ^ $past(out[2]))
    );

endmodule
