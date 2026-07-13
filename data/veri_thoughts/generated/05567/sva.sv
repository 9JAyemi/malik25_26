module Mflipflop_s_sva (
    input logic out,
    input logic in,
    input logic scanen,
    input logic sin,
    input logic clock,
    input logic reset
);

    // Reset high before the rising edge clears the sampled output low.
    check_reset_clears_out: assert property (
        @(posedge clock) reset |-> (out == 1'b0)
    );

    // With reset low, functional mode captures in on the next sampled edge.
    check_functional_capture: assert property (
        @(posedge clock) disable iff (reset)
        (!scanen) |=> (out == $past(in))
    );

    // With reset low, scan mode captures sin on the next sampled edge.
    check_scan_capture: assert property (
        @(posedge clock) disable iff (reset)
        scanen |=> (out == $past(sin))
    );

    // When inputs differ, scan mode must not capture the functional input.
    check_scan_selects_sin: assert property (
        @(posedge clock) disable iff (reset)
        (scanen && (sin != in)) |=> (out != $past(in))
    );

    // When inputs differ, functional mode must not capture the scan input.
    check_functional_selects_in: assert property (
        @(posedge clock) disable iff (reset)
        ((!scanen) && (sin != in)) |=> (out != $past(sin))
    );

endmodule