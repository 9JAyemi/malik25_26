module inc_module_sva (
    input logic clk,
    input logic reset,
    input logic [2:0] SW,
    input logic [3:0] LED
);
    // Clock: clk (posedge). Reset: reset (active-high, async). Sequential: LED <= prev(SW)+1 with 1-cycle latency.

    // While reset is asserted, LED is held at zero.
    check_reset_drives_led_zero: assert property (
        @(posedge clk) reset |-> (LED == 4'b0000)
    );

    // Out of reset, LED equals previous-cycle SW plus 1.
    check_led_from_prev_sw: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED == ({1'b0, $past(SW)} + 4'd1))
    );

    // Out of reset, LED[0] toggles vs previous SW[0].
    check_led_lsb_toggle: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED[0] == ~$past(SW[0]))
    );

    // Out of reset, LED[1] equals SW[1] XOR SW[0] from previous cycle.
    check_led_bit1_xor_prev: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED[1] == ($past(SW[1]) ^ $past(SW[0])))
    );

    // Out of reset, LED[2] equals SW[2] XOR (SW[1] & SW[0]) from previous cycle.
    check_led_bit2_carry_logic: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED[2] == ($past(SW[2]) ^ ($past(SW[1]) & $past(SW[0]))))
    );

    // Out of reset, LED[3] is the carry-out: SW[2] & SW[1] & SW[0] from previous cycle.
    check_led_msb_carry_from_prev: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED[3] == ($past(SW[2]) & $past(SW[1]) & $past(SW[0])))
    );

    // Out of reset, LED is never zero (since it is prev(SW)+1).
    check_led_nonzero_out_of_reset: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED != 4'd0)
    );

    // Out of reset, LED is in the range 1..8.
    check_led_in_range_out_of_reset: assert property (
        @(posedge clk) disable iff (reset)
            !$past(reset) |-> (LED inside {[4'd1:4'd8]})
    );

    // If SW was stable over the last two cycles (and not in reset), LED is stable this cycle.
    check_led_stable_when_sw_stable: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && !$past(reset,2) && ($past(SW) == $past(SW,2))) |-> (LED == $past(LED))
    );

    // If previous SW was 3'b111, LED[2:0] are zero (i.e., 8).
    check_led_lowbits_zero_on_overflow: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && (&$past(SW))) |-> (LED[2:0] == 3'b000)
    );
endmodule