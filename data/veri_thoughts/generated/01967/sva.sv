module sky130_fd_sc_lp__invkapwr_sva (
    input logic CLK,
    input logic Y,
    input logic A
);
    // Y is always the logical NOT of A.
    check_inversion: assert property (
        @(posedge CLK) (Y == ~A)
    );

    // When A is 0, Y must be 1.
    check_when_a0_y1: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == 1'b1)
    );

    // When A is 1, Y must be 0.
    check_when_a1_y0: assert property (
        @(posedge CLK) (A == 1'b1) |-> (Y == 1'b0)
    );

    // A and Y must never be equal at a sampling edge.
    check_never_equal: assert property (
        @(posedge CLK) (A != Y)
    );

    // Y only changes when A changes.
    check_y_change_implies_a_change: assert property (
        @(posedge CLK) $changed(Y) |-> $changed(A)
    );

    // A change implies Y changes.
    check_a_change_implies_y_change: assert property (
        @(posedge CLK) $changed(A) |-> $changed(Y)
    );

    // A rising edge causes Y to fall and be 0.
    check_a_rise_y_fall: assert property (
        @(posedge CLK) $rose(A) |-> ($fell(Y) && (Y == 1'b0))
    );

    // A falling edge causes Y to rise and be 1.
    check_a_fall_y_rise: assert property (
        @(posedge CLK) $fell(A) |-> ($rose(Y) && (Y == 1'b1))
    );

    // Y rising implies A fell and is 0.
    check_y_rise_a_fall: assert property (
        @(posedge CLK) $rose(Y) |-> ($fell(A) && (A == 1'b0))
    );

    // Y falling implies A rose and is 1.
    check_y_fall_a_rise: assert property (
        @(posedge CLK) $fell(Y) |-> ($rose(A) && (A == 1'b1))
    );
endmodule