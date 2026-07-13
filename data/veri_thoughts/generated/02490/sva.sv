module transition_capture_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    input logic [31:0] out,
    input logic [31:0] prev_in
);
    // On reset assertion, next cycle prev_in and out are zero.
    tc_reset_clears_regs: assert property (
        @(posedge clk) reset |=> (prev_in == 32'h0) && (out == 32'h0)
    );

    // While reset is held, regs remain zero.
    tc_hold_zero_during_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (prev_in == 32'h0) && (out == 32'h0)
    );

    // prev_in captures the input from the previous cycle (when not crossing reset).
    tc_prev_in_tracks_in: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (prev_in == $past(in))
    );

    // out updates per equation using previous-cycle values.
    tc_out_update_equation: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (out == (($past(prev_in) & ~ $past(in)) | $past(out)))
    );

    // out never clears bits outside reset.
    tc_out_no_clear: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (($past(out) & ~out) == 32'h0)
    );

    // If no 1->0 transitions in last cycle, out holds its value.
    tc_out_holds_when_no_fall: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (($past(prev_in) & ~ $past(in)) == 32'h0)) |-> (out == $past(out))
    );
endmodule

module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic [31:0] out
);
    // On reset assertion, next cycle top-level out is zero.
    top_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 32'h0)
    );

    // While reset is held, top-level out remains zero.
    top_hold_zero_during_reset: assert property (
        @(posedge clk) reset && $past(reset) |-> (out == 32'h0)
    );

    // Top-level out never clears bits outside reset.
    top_out_no_clear: assert property (
        @(posedge clk) disable iff (reset) !$past(reset) |-> (($past(out) & ~out) == 32'h0)
    );

    // Top-level out updates as previous out OR captured 1->0 transitions on in1/in2.
    top_out_update_from_inputs: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset)) |-> (
                out == ($past(out)
                        | ($past($past(in1)) & ~ $past(in1))
                        | ($past($past(in2)) & ~ $past(in2)))
            )
    );
endmodule