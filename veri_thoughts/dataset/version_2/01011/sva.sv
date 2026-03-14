module decade_counter_mux_sva (
    input logic clk,
    input logic slowena,
    input logic reset,      // active-low asynchronous reset
    input logic a,
    input logic b,
    input logic sel,
    input logic [7:0] out
);

    // Upper nibble of out is always zero due to 4-bit addition result.
    check_out_upper_nibble_zero: assert property (
        @(posedge clk) disable iff (!reset) (out[7:4] == 4'b0000)
    );

    // Lower nibble of out is always in the range 0..10 (count 0..9 plus selected 0/1).
    check_out_nibble_range: assert property (
        @(posedge clk) disable iff (!reset) (out[3:0] <= 4'd10)
    );

    // While reset is asserted low, out equals the selected input (count forced to 0).
    check_out_during_reset_matches_enable: assert property (
        @(posedge clk) (!reset) |-> ((out[7:1] == 7'b0) && (out[0] == ((sel == 1'b0) ? a : b)))
    );

    // When slowena is 0 and inputs are stable, out must hold.
    check_hold_when_slowena_low_inputs_stable: assert property (
        @(posedge clk) disable iff (!reset)
        ((slowena == 1'b0) && $stable(a) && $stable(b) && $stable(sel)) |=> $stable(out)
    );

    // When slowena is 1, inputs stable, and not at 9+enable, out increments by 1.
    check_increment_no_wrap: assert property (
        @(posedge clk) disable iff (!reset)
        ((slowena == 1'b1) && $stable(a) && $stable(b) && $stable(sel) &&
         (out[3:0] != (4'd9 + ((sel == 1'b0) ? a : b)))) |=> (out[3:0] == $past(out[3:0]) + 4'd1)
    );

    // When slowena is 1, inputs stable, and at 9+enable, out wraps to enable.
    check_wrap_to_enable: assert property (
        @(posedge clk) disable iff (!reset)
        ((slowena == 1'b1) && $stable(a) && $stable(b) && $stable(sel) &&
         (out[3:0] == (4'd9 + ((sel == 1'b0) ? a : b)))) |=> (out[3:0] == {3'b000, ((sel == 1'b0) ? a : b)})
    );

    // With slowena 1 and inputs stable, out must change (either +1 or wrap).
    check_out_changes_when_slowena_high: assert property (
        @(posedge clk) disable iff (!reset)
        ((slowena == 1'b1) && $stable(a) && $stable(b) && $stable(sel)) |=> (out != $past(out))
    );

    // If out is 10, the selected input must be 1 (only possible with enable=1 and count=9).
    check_out10_implies_enable1: assert property (
        @(posedge clk) disable iff (!reset)
        (out[3:0] == 4'd10) |-> (((sel == 1'b0) ? a : b) == 1'b1)
    );

    // If out is 0, the selected input must be 0 (only possible with enable=0 and count=0).
    check_out0_implies_enable0: assert property (
        @(posedge clk) disable iff (!reset)
        (out[3:0] == 4'd0) |-> (((sel == 1'b0) ? a : b) == 1'b0)
    );

    // If the selected input is 0, out cannot exceed 9.
    check_enable0_bounds_out: assert property (
        @(posedge clk) disable iff (!reset)
        (((sel == 1'b0) ? a : b) == 1'b0) |-> (out[3:0] <= 4'd9)
    );

    // If the selected input is 1, out is at least 1.
    check_enable1_bounds_out: assert property (
        @(posedge clk) disable iff (!reset)
        (((sel == 1'b0) ? a : b) == 1'b1) |-> (out[3:0] >= 4'd1)
    );

endmodule