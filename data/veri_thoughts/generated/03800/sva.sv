module top_module_sva (
    input logic [15:0] in,
    input logic clk,
    input logic reset,
    input logic [7:0] q
);

    // A reset cycle clears q by the next clock.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

    // While reset is held, q remains zero.
    check_held_reset_keeps_q_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (q == 8'h00)
    );

    // A non-reset cycle loads the upper byte of in into q.
    check_loads_upper_byte: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (q == $past(in[15:8]))
    );

    // Changing only the lower byte of in does not change q.
    check_lower_byte_is_ignored: assert property (
        @(posedge clk) disable iff (reset)
        (!$past(reset) && !$past(reset,2) &&
         ($past(in[15:8]) == $past(in[15:8],2)) &&
         ($past(in[7:0]) != $past(in[7:0],2)))
        |-> (q == $past(q))
    );

endmodule