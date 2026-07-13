module next_higher_binary_sva (
    input logic [3:0] in,
    input logic       clk,
    input logic [3:0] out
);

    // Sequential clk-only pipeline; the RTL has no reset.
    // out is the next-higher value of in sampled two clocks earlier.

    // 4'hF wraps to 4'h0 after the two-cycle pipeline.
    check_wrap_after_two_cycles: assert property (
        @(posedge clk) ($past(1'b1,2) && ($past(in,2) == 4'hF)) |-> (out == 4'h0)
    );

    // All other input values increment by one after the two-cycle pipeline.
    check_increment_after_two_cycles: assert property (
        @(posedge clk) ($past(1'b1,2) && ($past(in,2) != 4'hF)) |-> (out == ($past(in,2) + 4'd1))
    );

    // Repeating the delayed input value keeps the output stable.
    check_output_stable_when_delayed_input_repeats: assert property (
        @(posedge clk) ($past(1'b1,3) && ($past(in,2) == $past(in,3))) |-> $stable(out)
    );

    // Changing the delayed input value changes the output.
    check_output_changes_when_delayed_input_changes: assert property (
        @(posedge clk) ($past(1'b1,3) && ($past(in,2) != $past(in,3))) |-> !$stable(out)
    );

endmodule