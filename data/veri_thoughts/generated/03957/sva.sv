module regr_sva #(parameter N = 1) (
    input logic clk,
    input logic clear,
    input logic hold,
    input logic [N-1:0] in,
    input logic [N-1:0] out
);

    // Clear forces the register output to zero on the next clock.
    check_clear_sets_zero: assert property (
        @(posedge clk) clear |=> (out == {N{1'b0}})
    );

    // Clear takes priority over hold when both are asserted.
    check_clear_overrides_hold: assert property (
        @(posedge clk) (clear && hold) |=> (out == {N{1'b0}})
    );

    // Hold preserves the previous output value when clear is inactive.
    check_hold_preserves_out: assert property (
        @(posedge clk) disable iff (clear) hold |=> (out == $past(out))
    );

    // With clear low and hold low, the register captures the input.
    check_load_captures_in: assert property (
        @(posedge clk) disable iff (clear) !hold |=> (out == $past(in))
    );

endmodule