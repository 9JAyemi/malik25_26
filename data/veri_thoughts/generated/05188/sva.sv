module top_module_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic a,
    input logic b,
    input logic out_always_ff,
    input logic [2:0] shift_reg_out,
    input logic functional_module_out
);

    // Clock: clk; reset: active-high synchronous; logic: mixed sequential/combinational.

    // Reset clears the shift register on the following cycle.
    check_reset_clears_shift_register: assert property (
        @(posedge clk) reset |=> (shift_reg_out == 3'b000)
    );

    // Reset clears the top-level output flop on the following cycle.
    check_reset_clears_out_always_ff: assert property (
        @(posedge clk) reset |=> (out_always_ff == 1'b0)
    );

    // Reset forces the functional output low through the cleared shift register.
    check_reset_clears_functional_output: assert property (
        @(posedge clk) reset |=> (functional_module_out == 1'b0)
    );

    // The shift register shifts left and loads d into bit 0 each cycle.
    check_shift_register_update: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (shift_reg_out == {$past(shift_reg_out[1:0]), $past(d)})
    );

    // The functional output matches shift_reg_out[2] AND (a XOR b).
    check_functional_module_logic: assert property (
        @(posedge clk) disable iff (reset)
        (functional_module_out == (shift_reg_out[2] & (a ^ b)))
    );

    // When the flop was low, it captures functional_module_out on the next cycle.
    check_out_ff_captures_functional_output: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && !$past(out_always_ff)) |-> (out_always_ff == $past(functional_module_out))
    );

    // When the flop was high, it clears on the next cycle.
    check_out_ff_clears_after_high: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && $past(out_always_ff)) |-> (out_always_ff == 1'b0)
    );

endmodule