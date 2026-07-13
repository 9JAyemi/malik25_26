module regr_sva #(parameter N = 1) (
    input logic         clk,
    input logic         rst,
    input logic         clear,
    input logic         hold,
    input logic [N-1:0] in,
    input logic [N-1:0] out
);

    // Active-low reset clears the register by the next sampled cycle.
    check_reset_forces_zero: assert property (
        @(posedge clk)
        !rst |=> (out == {N{1'b0}})
    );

    // Clear drives the register to zero.
    check_clear_forces_zero: assert property (
        @(posedge clk) disable iff (!rst)
        clear |=> (out == {N{1'b0}})
    );

    // Clear takes priority over hold.
    check_clear_overrides_hold: assert property (
        @(posedge clk) disable iff (!rst)
        (clear && hold) |=> (out == {N{1'b0}})
    );

    // Hold preserves the current register value when clear is low.
    check_hold_preserves_value: assert property (
        @(posedge clk) disable iff (!rst)
        (hold && !clear) |=> (out == $past(out))
    );

    // With neither clear nor hold, the input is captured.
    check_load_captures_input: assert property (
        @(posedge clk) disable iff (!rst)
        (!clear && !hold) |=> (out == $past(in))
    );

endmodule