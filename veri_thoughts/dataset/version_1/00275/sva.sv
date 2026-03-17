module add_subtract_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic sel,
    input logic [7:0] out
);

    // In add mode, the output is the 8-bit sum of a and b.
    check_add_mode_result: assert property (
        @(posedge clk) sel |-> (out == (a + b))
    );

    // In subtract mode, the output is the 8-bit difference of a and b.
    check_subtract_mode_result: assert property (
        @(posedge clk) !sel |-> (out == (a - b))
    );

    // If all inputs stay the same, the output stays the same.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(sel)) |-> $stable(out)
    );

    // A select change with stable operands updates output to the newly selected result.
    check_select_change_updates_result: assert property (
        @(posedge clk) ($changed(sel) && $stable(a) && $stable(b)) |-> (out == (sel ? (a + b) : (a - b)))
    );

    // Addition wraps around on 8-bit overflow.
    check_add_overflow_wrap: assert property (
        @(posedge clk) (sel && (a == 8'hff) && (b == 8'h01)) |-> (out == 8'h00)
    );

    // Subtraction wraps around on 8-bit underflow.
    check_subtract_underflow_wrap: assert property (
        @(posedge clk) (!sel && (a == 8'h00) && (b == 8'h01)) |-> (out == 8'hff)
    );

endmodule