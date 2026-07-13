module reg4_sva (
    input logic clk,
    input logic rst_l,
    input logic [3:0] d,
    input logic [3:0] q
);
    ///// Reset behavior /////
    // While reset is asserted low, q must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) (!rst_l) |-> (q == 4'b0000)
    );

    // If reset stays low across two cycles, q remains 0 and stable.
    check_reset_hold_zero: assert property (
        @(posedge clk) (!rst_l && $past(!rst_l)) |-> (q == 4'b0000) && $stable(q)
    );

    ///// Data capture behavior /////
    // When not in reset for two cycles, q equals previous cycle's d.
    check_capture_prev_d: assert property (
        @(posedge clk) disable iff (!rst_l) $past(rst_l) |-> (q == $past(d))
    );

    // On a reset deassertion, next cycle q reflects d from the deassertion cycle.
    check_after_release_next_matches_current_d: assert property (
        @(posedge clk) disable iff (!rst_l) $rose(rst_l) |-> ##1 (q == $past(d))
    );

    // If d is unchanged across a cycle and not in reset previously, q equals d.
    check_q_equals_d_when_d_stable: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && (d == $past(d))) |-> (q == d)
    );

    // If q differs from d (and wasn't in reset previously), d must have changed this cycle.
    check_q_ne_d_implies_d_changed: assert property (
        @(posedge clk) disable iff (!rst_l) ($past(rst_l) && (q != d)) |-> (d != $past(d))
    );

    ///// Bit-level transition correlation /////
    // A rise on q[i] implies previous d[i] was 1 (no reset in prior cycle).
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_bit_checks
            check_q_bit_rise_implies_prev_d1: assert property (
                @(posedge clk) disable iff (!rst_l) ($past(rst_l) && $rose(q[i])) |-> ($past(d[i]) == 1'b1)
            );
            // A fall on q[i] implies previous d[i] was 0 (no reset in prior cycle).
            check_q_bit_fall_implies_prev_d0: assert property (
                @(posedge clk) disable iff (!rst_l) ($past(rst_l) && $fell(q[i])) |-> ($past(d[i]) == 1'b0)
            );
        end
    endgenerate
endmodule