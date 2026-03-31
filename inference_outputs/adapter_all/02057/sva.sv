module shift_register_sva (
    input logic clk,
    input logic in,
    input logic shift,
    input logic out
);

    // Output reflects the bit shifted in on the previous shift edge.
    check_output_shifts_previous_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$initstate && !$isunknown($past(in))) |-> (out == $past(in))
    );

    // A high output must come from a high input on the previous shift edge.
    check_high_output_requires_high_previous_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$initstate && !$isunknown($past(in)) && out) |-> $past(in)
    );

    // A low output must come from a low input on the previous shift edge.
    check_low_output_requires_low_previous_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$initstate && !$isunknown($past(in)) && !out) |-> !$past(in)
    );

    // A rising output must come from a rising input on the previous shift edge.
    check_rising_output_requires_rising_previous_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$initstate && !$isunknown($past(in)) && $rose(out)) |-> $rose($past(in))
    );

    // A falling output must come from a falling input on the previous shift edge.
    check_falling_output_requires_falling_previous_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$initstate && !$isunknown($past(in)) && $fell(out)) |-> $fell($past(in))
    );

endmodule