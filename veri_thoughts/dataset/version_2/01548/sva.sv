module bm_dag2_log_mod_sva (
    input logic        clock,
    input logic        reset_n,
    input logic [1:0]  a_in,
    input logic [1:0]  b_in,
    input logic        c_in,
    input logic        d_in,
    input logic [1:0]  out0,
    input logic        out1
);
    // out0 equals previous cycle's bitwise AND of a_in and b_in.
    check_out0_matches_past_a_and_b: assert property (
        @(posedge clock) disable iff (!reset_n) $past(reset_n) |-> (out0 == ($past(a_in) & $past(b_in)))
    );

    // out1 equals previous cycle's AND of c_in and d_in.
    check_out1_matches_past_c_and_d: assert property (
        @(posedge clock) disable iff (!reset_n) $past(reset_n) |-> (out1 == ($past(c_in) & $past(d_in)))
    );

    // No out0 bit can be 1 unless the corresponding past a_in bit was 1.
    check_out0_requires_past_a_high_for_ones: assert property (
        @(posedge clock) disable iff (!reset_n) $past(reset_n) |-> ((out0 & ~ $past(a_in)) == 2'b00)
    );

    // No out0 bit can be 1 unless the corresponding past b_in bit was 1.
    check_out0_requires_past_b_high_for_ones: assert property (
        @(posedge clock) disable iff (!reset_n) $past(reset_n) |-> ((out0 & ~ $past(b_in)) == 2'b00)
    );

    // If past a_in was 2'b00 then out0 must be 2'b00.
    check_out0_zero_when_past_a_zero: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && ($past(a_in) == 2'b00)) |-> (out0 == 2'b00)
    );

    // If past b_in was 2'b00 then out0 must be 2'b00.
    check_out0_zero_when_past_b_zero: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && ($past(b_in) == 2'b00)) |-> (out0 == 2'b00)
    );

    // No out0 bit can be 1 if that bit was 0 in the past (a_in | b_in).
    check_out0_masked_by_past_or: assert property (
        @(posedge clock) disable iff (!reset_n) $past(reset_n) |-> ((out0 & ~ $past(a_in | b_in)) == 2'b00)
    );

    // If either past c_in or past d_in was 0 then out1 must be 0.
    check_out1_zero_when_any_past_input_zero: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && ((!$past(c_in)) || (!$past(d_in)))) |-> (!out1)
    );

    // out0 holds next cycle when a_in and b_in are stable this cycle.
    check_out0_stable_when_ab_stable: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && $stable(a_in) && $stable(b_in)) |=> (out0 == $past(out0))
    );

    // out1 holds next cycle when c_in and d_in are stable this cycle.
    check_out1_stable_when_cd_stable: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && $stable(c_in) && $stable(d_in)) |=> (out1 == $past(out1))
    );

    // A rise on out1 requires both c_in and d_in were 1 in the previous cycle.
    check_out1_rise_requires_past_cd_high: assert property (
        @(posedge clock) disable iff (!reset_n) ($past(reset_n) && $rose(out1)) |-> ($past(c_in) && $past(d_in))
    );
endmodule