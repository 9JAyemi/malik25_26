module flip_flops_sva (
    input logic clk,
    input logic d,
    input logic j,
    input logic k,
    input logic t,
    input logic s,
    input logic r,
    input logic rst,
    input logic q_d,
    input logic q_jk,
    input logic q_t,
    input logic q_sr
);

    // A sampled reset cycle clears all flip-flop outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (q_d == 1'b0) && (q_jk == 1'b0) && (q_t == 1'b0) && (q_sr == 1'b0)
    );

    // The D flip-flop captures d on each active clock edge.
    check_dff_captures_d: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (q_d == $past(d))
    );

    // The JK flip-flop toggles when both j and k are high.
    check_jkff_toggles_when_jk_high: assert property (
        @(posedge clk) disable iff (rst) (j && k) |=> (q_jk == ~$past(q_jk))
    );

    // The JK flip-flop holds its state when j and k are not both high.
    check_jkff_holds_when_not_jk_high: assert property (
        @(posedge clk) disable iff (rst) (!(j && k)) |=> (q_jk == $past(q_jk))
    );

    // The T flip-flop toggles when t is high.
    check_tff_toggles_when_t_high: assert property (
        @(posedge clk) disable iff (rst) t |=> (q_t == ~$past(q_t))
    );

    // The T flip-flop holds its state when t is low.
    check_tff_holds_when_t_low: assert property (
        @(posedge clk) disable iff (rst) (!t) |=> (q_t == $past(q_t))
    );

    // The SR flip-flop sets when s is high and r is low.
    check_srff_sets_when_s_high_r_low: assert property (
        @(posedge clk) disable iff (rst) (s && !r) |=> (q_sr == 1'b1)
    );

    // The SR flip-flop clears when s is low and r is high.
    check_srff_clears_when_s_low_r_high: assert property (
        @(posedge clk) disable iff (rst) (!s && r) |=> (q_sr == 1'b0)
    );

    // The SR flip-flop holds its state when s and r are equal.
    check_srff_holds_when_s_equals_r: assert property (
        @(posedge clk) disable iff (rst) ((s && r) || (!s && !r)) |=> (q_sr == $past(q_sr))
    );

endmodule