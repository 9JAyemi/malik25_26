module dff_sr_sva (
    input logic CK,
    input logic D,
    input logic S,
    input logic R,
    input logic Q,
    input logic QN
);

    // Clock: CK. No reset is present in the RTL.
    // Q is sequential; QN is combinationally driven as ~Q.

    // QN must always be the complement of Q.
    check_qn_complement: assert property (
        @(posedge CK) QN === ~Q
    );

    // S asserted at a clock edge forces Q high on that update.
    check_sync_set: assert property (
        @(posedge CK) S |=> (Q === 1'b1)
    );

    // When both S and R are asserted, set has priority.
    check_set_priority_over_reset: assert property (
        @(posedge CK) (S && R) |=> (Q === 1'b1)
    );

    // R asserted without S forces Q low on that update.
    check_sync_reset: assert property (
        @(posedge CK) (!S && R) |=> (Q === 1'b0)
    );

    // With S and R deasserted, D=1 is captured into Q.
    check_data_capture_one: assert property (
        @(posedge CK) (!S && !R && D) |=> (Q === 1'b1)
    );

    // With S and R deasserted, D=0 is captured into Q.
    check_data_capture_zero: assert property (
        @(posedge CK) (!S && !R && !D) |=> (Q === 1'b0)
    );

endmodule