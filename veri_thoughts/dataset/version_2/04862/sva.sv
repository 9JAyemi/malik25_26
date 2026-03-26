module gated_D_flipflop_sva (
    input logic clk,
    input logic clr,
    input logic en,
    input logic d,
    input logic q,
    input logic qn
);

    // Active-low clear forces q low and qn high.
    check_sync_clear_values: assert property (
        @(posedge clk) (!clr) |=> (q == 1'b0 && qn == 1'b1)
    );

    // Clear overrides enable when both are asserted.
    check_clear_priority_over_enable: assert property (
        @(posedge clk) ((!clr) && en) |=> (q == 1'b0 && qn == 1'b1)
    );

    // When enabled, q captures d.
    check_enable_captures_d_to_q: assert property (
        @(posedge clk) disable iff (!clr) en |=> (q == $past(d))
    );

    // When enabled, qn captures the inverse of d.
    check_enable_captures_inv_d_to_qn: assert property (
        @(posedge clk) disable iff (!clr) en |=> (qn == ~$past(d))
    );

    // When enabled, q and qn remain complementary.
    check_enable_outputs_complementary: assert property (
        @(posedge clk) disable iff (!clr) en |=> (qn == ~q)
    );

    // When disabled, q holds its value.
    check_hold_q_when_disabled: assert property (
        @(posedge clk) disable iff (!clr) (!en) |=> (q == $past(q))
    );

    // When disabled, qn holds its value.
    check_hold_qn_when_disabled: assert property (
        @(posedge clk) disable iff (!clr) (!en) |=> (qn == $past(qn))
    );

endmodule