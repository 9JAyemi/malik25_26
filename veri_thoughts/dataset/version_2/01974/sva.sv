module d_flip_flop_mux_latch_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic mux_out,
    input logic latch_out
);
    // Clock: clk (posedge). No reset present.
    // Mixed logic: sequential FFs for mux_out and q; combinational mirror latch_out from mux_out.
    // Function: pipeline d -> mux_out (FF) -> latch_out (comb) -> q (FF).

    // mux_out captures D on the prior clock edge.
    check_muxout_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (mux_out == $past(d))
    );

    // latch_out mirrors mux_out at each sampled clock (after initial cycle).
    check_latch_mirrors_mux: assert property (
        @(posedge clk) 1'b1 |=> (latch_out == mux_out)
    );

    // q captures latch_out from the prior clock edge.
    check_q_captures_latch: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(latch_out))
    );

    // q equals the previous-cycle value of mux_out.
    check_q_equals_past_mux: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(mux_out))
    );

    // If mux_out rises between samples, latch_out also rises.
    check_mux_rise_implies_latch_rise: assert property (
        @(posedge clk) 1'b1 |=> ($rose(mux_out) |-> $rose(latch_out))
    );

    // If latch_out rises between samples, mux_out also rises.
    check_latch_rise_implies_mux_rise: assert property (
        @(posedge clk) 1'b1 |=> ($rose(latch_out) |-> $rose(mux_out))
    );

    // If mux_out falls between samples, latch_out also falls.
    check_mux_fall_implies_latch_fall: assert property (
        @(posedge clk) 1'b1 |=> ($fell(mux_out) |-> $fell(latch_out))
    );

    // If latch_out falls between samples, mux_out also falls.
    check_latch_fall_implies_mux_fall: assert property (
        @(posedge clk) 1'b1 |=> ($fell(latch_out) |-> $fell(mux_out))
    );

endmodule