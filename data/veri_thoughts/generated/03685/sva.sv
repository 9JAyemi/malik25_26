module clk_phase_shifter_sva (
    input logic clk,
    input logic [7:0] shift,
    input logic clk_shifted,
    input logic [7:0] shift_reg,
    input logic [7:0] shift_reg_next,
    input logic [7:0] shift_reg_last,
    input logic clk_shifted_last
);
    localparam int n = 8;

    // shift_reg_last captures the previous cycle's shift_reg.
    check_shift_reg_last_tracks_shift_reg: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg_last === $past(shift_reg))
    );

    // clk_shifted_last captures the previous cycle's clk_shifted.
    check_clk_shifted_last_tracks_clk_shifted: assert property (
        @(posedge clk) 1'b1 |=> (clk_shifted_last === $past(clk_shifted))
    );

    // The LSB of shift_reg_next is loaded HIGH because clk is HIGH at posedge.
    check_shift_reg_next_lsb_loads_clock_high: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg_next[0] === 1'b1)
    );

    // The upper bits of shift_reg_next shift in the previous shift_reg value.
    check_shift_reg_next_upper_bits_shift_previous_reg: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg_next[n-1:1] === $past(shift_reg[n-2:0]))
    );

    // shift_reg captures the previous cycle's shift_reg_next.
    check_shift_reg_tracks_previous_next: assert property (
        @(posedge clk) 1'b1 |=> (shift_reg === $past(shift_reg_next))
    );

    // A zero shift selection forces clk_shifted HIGH on the next sampled cycle.
    check_zero_shift_drives_high_next_cycle: assert property (
        @(posedge clk) (shift == 8'h00) |=> (clk_shifted === 1'b1)
    );

    // A nonzero shift selection uses the previous cycle's shift_reg_last MSB.
    check_nonzero_shift_uses_delayed_tap: assert property (
        @(posedge clk) (shift != 8'h00) |=> (clk_shifted === $past(shift_reg_last[n-1]))
    );

    // After 16 cycles, shift_reg is fully filled with ones.
    check_shift_reg_eventually_all_ones: assert property (
        @(posedge clk) 1'b1 |=> ##15 (shift_reg === 8'hFF)
    );

    // After 17 cycles, shift_reg_last is fully filled with ones.
    check_shift_reg_last_eventually_all_ones: assert property (
        @(posedge clk) 1'b1 |=> ##16 (shift_reg_last === 8'hFF)
    );

    // After 18 cycles, clk_shifted is driven HIGH regardless of shift.
    check_clk_shifted_eventually_high: assert property (
        @(posedge clk) 1'b1 |=> ##17 (clk_shifted === 1'b1)
    );

endmodule