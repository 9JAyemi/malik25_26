module reverse_last_two_bits_assertions (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // Single clocked process; no reset is present in the RTL.
    // The 4-bit concatenation is truncated to 2 bits, so out captures in[3:2].

    // Out captures the previous cycle's upper input bits.
    check_out_captures_prev_upper_bits: assert property (
        @(posedge clk) !$initstate |-> (out == $past(in[3:2]))
    );

    // Out[0] comes from the previous cycle's in[2].
    check_out_bit0_from_prev_in2: assert property (
        @(posedge clk) !$initstate |-> (out[0] == $past(in[2]))
    );

    // Out[1] comes from the previous cycle's in[3].
    check_out_bit1_from_prev_in3: assert property (
        @(posedge clk) !$initstate |-> (out[1] == $past(in[3]))
    );

    // If upper input bits hold, out matches the current upper bits.
    check_out_matches_current_when_upper_bits_hold: assert property (
        @(posedge clk)
        (!$initstate && (in[3:2] == $past(in[3:2]))) |-> (out == in[3:2])
    );

    // If upper input bits change, out still reflects the previous sample.
    check_out_differs_from_current_when_upper_bits_change: assert property (
        @(posedge clk)
        (!$initstate && (in[3:2] != $past(in[3:2]))) |-> (out != in[3:2])
    );

    // Changing only lower input bits does not affect out.
    check_lower_bit_changes_do_not_affect_out: assert property (
        @(posedge clk)
        (!$initstate &&
         (in[3:2] == $past(in[3:2])) &&
         (in[1:0] != $past(in[1:0]))) |-> (out == in[3:2])
    );

    // When only upper input bits change, out remains one cycle behind them.
    check_only_upper_bit_changes_show_one_cycle_latency: assert property (
        @(posedge clk)
        (!$initstate &&
         (in[1:0] == $past(in[1:0])) &&
         (in[3:2] != $past(in[3:2]))) |-> (out == $past(in[3:2]))
    );

endmodule