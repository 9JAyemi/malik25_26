module top_module_sva (
    input logic       clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic       sel,
    input logic       reset,
    input logic [7:0] q,
    input logic [7:0] flip_flop_out,
    input logic [7:0] multiplier_out
);

    // Clock: clk; reset: reset (active-high asynchronous).
    // Mixed sequential/combinational datapath.

    // sel=0 forces multiplier_out to zero.
    check_multiplier_zero_when_sel_low: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b0) |-> (multiplier_out == 8'b0)
    );

    // sel=1 passes d2 onto multiplier_out.
    check_multiplier_passes_d2_when_sel_high: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b1) |-> (multiplier_out == d2)
    );

    // q mirrors the internal register value.
    check_q_matches_flip_flop_out: assert property (
        @(posedge clk) disable iff (reset)
        (q == flip_flop_out)
    );

    // With sel low, the register captures d1 on the next clock.
    check_load_d1_when_sel_low: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b0) |=> (flip_flop_out == $past(d1))
    );

    // With sel high, the register captures d2 on the next clock.
    check_load_d2_when_sel_high: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b1) |=> (flip_flop_out == $past(d2))
    );

    // With sel low, q shows the prior d1 value on the next clock.
    check_q_captures_d1_when_sel_low: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b0) |=> (q == $past(d1))
    );

    // With sel high, q shows the prior d2 value on the next clock.
    check_q_captures_d2_when_sel_high: assert property (
        @(posedge clk) disable iff (reset)
        (sel == 1'b1) |=> (q == $past(d2))
    );

    // A reset cycle leaves the internal register cleared on the next clock.
    check_flip_flop_out_cleared_after_reset: assert property (
        @(posedge clk)
        reset |=> (flip_flop_out == 8'b0)
    );

    // A reset cycle leaves q cleared on the next clock.
    check_q_cleared_after_reset: assert property (
        @(posedge clk)
        reset |=> (q == 8'b0)
    );

endmodule