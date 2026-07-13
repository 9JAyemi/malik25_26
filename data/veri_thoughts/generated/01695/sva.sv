module sky130_fd_sc_hdll__clkinv_sva (
    input logic clk,
    input logic Y,
    input logic A
);
    // Y is always the logical inversion of A.
    check_inversion_function: assert property (
        @(posedge clk) (Y == ~A)
    );

    // When A is 0, Y is 1 in the same cycle.
    check_a0_y1: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b1)
    );

    // When A is 1, Y is 0 in the same cycle.
    check_a1_y0: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // Y is never equal to A.
    check_never_equal: assert property (
        @(posedge clk) (Y != A)
    );

    // A rising edge implies Y falls.
    check_riseA_fallY: assert property (
        @(posedge clk) $rose(A) |-> $fell(Y)
    );

    // A falling edge implies Y rises.
    check_fallA_riseY: assert property (
        @(posedge clk) $fell(A) |-> $rose(Y)
    );

    // Y rising edge implies A fell.
    check_riseY_fallA: assert property (
        @(posedge clk) $rose(Y) |-> $fell(A)
    );

    // Y falling edge implies A rose.
    check_fallY_riseA: assert property (
        @(posedge clk) $fell(Y) |-> $rose(A)
    );

    // Any change on A causes a change on Y at the next sample.
    check_changeA_changeY: assert property (
        @(posedge clk) $changed(A) |-> $changed(Y)
    );

    // Any change on Y corresponds to a change on A.
    check_changeY_changeA: assert property (
        @(posedge clk) $changed(Y) |-> $changed(A)
    );

    // If A is stable, Y must be stable.
    check_stableA_stableY: assert property (
        @(posedge clk) $stable(A) |-> $stable(Y)
    );

    // If Y is stable, A must be stable.
    check_stableY_stableA: assert property (
        @(posedge clk) $stable(Y) |-> $stable(A)
    );
endmodule