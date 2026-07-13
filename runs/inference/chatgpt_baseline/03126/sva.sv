module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic [31:0] out
);

    // Reset forces the output low.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 32'h0000_0000)
    );

    // A zero input cannot produce any output pulse.
    check_zero_input_gives_zero_out: assert property (
        @(posedge clk) disable iff (reset)
        (in == 32'h0000_0000) |-> (out == 32'h0000_0000)
    );

    // Output bits can only be high when the corresponding input bits are high.
    check_output_only_when_input_high: assert property (
        @(posedge clk) disable iff (reset)
        ((out & ~in) == 32'h0000_0000)
    );

    // The first cycle after reset uses a cleared previous state.
    check_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(reset) |-> (out == in)
    );

    // After an active cycle, out is the rising-edge mask of in.
    check_rising_edge_function: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset) |-> (out == (in & ~$past(in)))
    );

    // Stable inputs do not generate output pulses.
    check_stable_input_no_pulse: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        ($past(!reset) && (in == $past(in))) |-> (out == 32'h0000_0000)
    );

    // Bits that were high in the previous cycle cannot pulse again immediately.
    check_prev_high_bits_do_not_pulse: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset) |-> ((out & $past(in)) == 32'h0000_0000)
    );

endmodule