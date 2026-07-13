module add_sub_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       mode,
    input logic [3:0] result
);
    // Clock: posedge mode; Reset: none; Mixed logic (combinational sum/diff, sequential update on mode rise).

    // On mode rising edge, next sampled result equals current (a - b) mod 16.
    update_on_mode_rise_captures_diff_next: assert property (
        @(posedge mode) 1'b1 |=> (result == $past((a - b)[3:0]))
    );

    // At a mode rising edge after the first, current result equals previous (a - b) mod 16.
    hold_result_matches_prev_diff: assert property (
        @(posedge mode) $past($rose(mode)) |-> (result == $past((a - b)[3:0]))
    );

    // If a == b at a rising edge, next sampled result is 0.
    equal_operands_zero: assert property (
        @(posedge mode) (a == b) |=> (result == 4'd0)
    );

    // If b == 0 at a rising edge, next sampled result equals a.
    b_zero_passthrough_a: assert property (
        @(posedge mode) (b == 4'd0) |=> (result == $past(a))
    );

    // If a == 0 at a rising edge, next sampled result equals (0 - b) mod 16.
    a_zero_twos_complement_b: assert property (
        @(posedge mode) (a == 4'd0) |=> (result == $past((4'd0 - b)[3:0]))
    );

    // If inputs are unchanged vs previous rising edge, next sampled result is unchanged.
    unchanged_inputs_preserve_result: assert property (
        @(posedge mode) $past($rose(mode)) && (a == $past(a)) && (b == $past(b)) |=> (result == $past(result))
    );

    // If b == (a + 1) mod 16 at a rising edge, next sampled result is 0xF.
    b_eq_a_plus1_yields_F: assert property (
        @(posedge mode) (((a + 4'd1)[3:0]) == b) |=> (result == 4'hF)
    );

    // If b == (a - 1) mod 16 at a rising edge, next sampled result is 0x1.
    b_eq_a_minus1_yields_1: assert property (
        @(posedge mode) (((a - 4'd1)[3:0]) == b) |=> (result == 4'h1)
    );

    // When sum != diff at a rising edge, next sampled result is not the sum.
    next_result_not_sum_when_sum_ne_diff: assert property (
        @(posedge mode) (((a + b)[3:0]) != ((a - b)[3:0])) |=> (result != $past((a + b)[3:0]))
    );

    // If current diff equals previous diff, current result equals previous result (before update).
    consistent_diff_implies_stable_result_now: assert property (
        @(posedge mode) $past($rose(mode)) && (((a - b)[3:0]) == $past((a - b)[3:0])) |-> (result == $past(result))
    );
endmodule