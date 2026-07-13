module johnson_counter_sva #(
    parameter int n = 4
)(
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out,
    input logic [n-1:0] q
);

    // Sampled reset clears both registers by the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |=> ((q == {n{1'b0}}) && (out == {n{1'b0}}))
    );

    // The all-zero state is absorbing in normal operation.
    check_zero_state_is_absorbing: assert property (
        @(posedge clk) disable iff (rst)
        ((q == {n{1'b0}}) && (out == {n{1'b0}})) |=> ((q == {n{1'b0}}) && (out == {n{1'b0}}))
    );

    // Outside sampled reset, q is always the rotated form of out on the next cycle.
    check_q_matches_rotated_out: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (q == {out[n-2:0], out[n-1]})
    );

    // Outside sampled reset, out either captures the previous q or both registers are reset to zero.
    check_out_tracks_previous_q_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> ((out == $past(q)) || ((q == {n{1'b0}}) && (out == {n{1'b0}})))
    );

    // The next sampled state is either the normal shift/capture update or the zeroed reset state.
    check_full_state_update_or_zero: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (((q == {n{1'b0}}) && (out == {n{1'b0}})) ||
                  ((q == {$past(q[n-2:0]), $past(q[n-1])}) && (out == $past(q))))
    );

endmodule