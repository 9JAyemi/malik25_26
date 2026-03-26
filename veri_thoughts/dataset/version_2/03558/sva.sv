module dff_asynchronous_set_reset_sva (
    input logic clk,
    input logic rst,
    input logic set,
    input logic d,
    input logic q,
    input logic qn
);

    // qn complements q during normal operation.
    check_qn_complements_q: assert property (
        @(posedge clk) disable iff (!rst) (qn == ~q)
    );

    // Active-low reset forces q low.
    check_reset_forces_q_low: assert property (
        @(posedge clk) (!rst) |-> (q == 1'b0)
    );

    // Active-low reset forces qn high.
    check_reset_forces_qn_high: assert property (
        @(posedge clk) (!rst) |-> (qn == 1'b1)
    );

    // q remains low on the first clock after reset was active.
    check_post_reset_q_stays_low: assert property (
        @(posedge clk) disable iff (!rst) (!$initstate && $past(!rst)) |-> (q == 1'b0)
    );

    // qn remains high on the first clock after reset was active.
    check_post_reset_qn_stays_high: assert property (
        @(posedge clk) disable iff (!rst) (!$initstate && $past(!rst)) |-> (qn == 1'b1)
    );

endmodule