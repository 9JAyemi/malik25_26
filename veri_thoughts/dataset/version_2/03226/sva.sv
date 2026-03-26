module triangular_wave_sva (
    input logic       clk,
    input logic [7:0] out,
    input logic [7:0] count,
    input logic [7:0] slope,
    input logic [7:0] peak
);

    // Slope is initialized to 1 and never changes.
    check_slope_is_one: assert property (
        @(posedge clk) slope == 8'd1
    );

    // Peak is initialized to 255 and never changes.
    check_peak_is_ff: assert property (
        @(posedge clk) peak == 8'hFF
    );

    // Count increments by one on every clock, wrapping modulo 256.
    check_count_advances: assert property (
        @(posedge clk) 1'b1 |=> count == ($past(count) + 8'd1)
    );

    // When count is zero, the next cycle drives out to zero and count to one.
    check_zero_branch: assert property (
        @(posedge clk) (count == 8'd0) |=> (out == 8'd0) && (count == 8'd1)
    );

    // When count reaches peak, the next cycle drives truncated 2*peak and wraps count.
    check_peak_branch: assert property (
        @(posedge clk) (count == peak) |=> (out == (peak + peak)) && (count == 8'd0)
    );

    // Outside the special count values, out increments by slope.
    check_increment_branch: assert property (
        @(posedge clk) (count != 8'd0 && count != peak) |=> (out == ($past(out) + $past(slope)))
    );

    // For nonzero count values, out matches count minus one.
    check_nonzero_count_matches_out: assert property (
        @(posedge clk) (count != 8'd0) |-> (out == (count - 8'd1))
    );

endmodule