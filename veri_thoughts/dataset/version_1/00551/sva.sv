module detect_0_to_1_assertions (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic [31:0] out
);

    // A reset cycle forces out low on the following sample.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 32'b0)
    );

    // The first active cycle after reset compares input against zero.
    check_first_active_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |=> (out == $past(in))
    );

    // Active cycles detect 0-to-1 transitions from the prior input.
    check_detects_zero_to_one_transitions: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |=> (out == ($past(in) & ~$past(in,2)))
    );

    // Output bits can only come from 1 bits in the generating input.
    check_out_is_subset_of_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((out & ~$past(in)) == 32'b0)
    );

    // An all-zero input produces an all-zero output.
    check_zero_input_produces_zero_out: assert property (
        @(posedge clk) disable iff (reset)
        (in == 32'b0) |=> (out == 32'b0)
    );

    // Stable input across active cycles produces no detection pulse.
    check_stable_input_produces_zero_out: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && (in == $past(in))) |=> (out == 32'b0)
    );

    // Bits that were already high in the prior input do not retrigger.
    check_previous_ones_do_not_retrigger: assert property (
        @(posedge clk) disable iff (reset)
        !$past(reset) |=> ((out & $past(in,2)) == 32'b0)
    );

endmodule