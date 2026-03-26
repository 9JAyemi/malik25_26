module message_display_system_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  message,
    input logic [15:0] display
);

    // Reset clears the display by the next sampled cycle.
    check_reset_clears_display: assert property (
        @(posedge clk) reset |=> (display == 16'b0)
    );

    // The upper 15 display bits shift from the prior lower 15 bits.
    check_display_upper_bits_shift: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        1'b1 |=> (display[15:1] == $past(display[14:0]))
    );

    // A lower nibble of 4'hF shifts a 1 into display bit 0.
    check_lsb_loads_one_on_f: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (message[3:0] === 4'hF) |=> (display[0] == 1'b1)
    );

    // Any lower nibble other than 4'hF shifts a 0 into display bit 0.
    check_lsb_loads_zero_otherwise: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (message[3:0] !== 4'hF) |=> (display[0] == 1'b0)
    );

    // Sixteen consecutive zero inserts clear all prior display contents.
    check_sixteen_zero_inserts_clear_display: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((message[3:0] !== 4'hF)[*16]) |=> (display == 16'b0)
    );

    // Sixteen consecutive one inserts fill the display with ones.
    check_sixteen_one_inserts_fill_display: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ((message[3:0] === 4'hF)[*16]) |=> (display == 16'hFFFF)
    );

endmodule