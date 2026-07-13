module counter_assertions (
    input logic clk,
    input logic reset,
    input logic [3:0] N,
    input logic [3:0] out
);

    // When reset is high, out is zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) reset |-> (out == 4'b0000)
    );

    // A terminal-count match drives the next sampled value to zero.
    check_match_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset) (out == N) |=> (out == 4'b0000)
    );

    // A non-match advances by one, unless async reset forces zero between clocks.
    check_nonmatch_advances_or_resets: assert property (
        @(posedge clk) disable iff (reset)
            (out != N) |=> ((out == 4'b0000) || (out == ($past(out) + 4'b0001)))
    );

    // Incrementing from 4'hF wraps the 4-bit counter to zero.
    check_overflow_wraps_to_zero: assert property (
        @(posedge clk) disable iff (reset) (out == 4'hF && N != 4'hF) |=> (out == 4'b0000)
    );

    // A nonzero, nonterminal count cannot repeat on the next sampled cycle.
    check_nonterminal_nonzero_changes: assert property (
        @(posedge clk) disable iff (reset) (out != 4'b0000 && out != N) |=> (out != $past(out))
    );

endmodule