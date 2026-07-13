module mux4to1_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1
);

    // Combinational RTL is sampled on an external verification clock.

    // Y is implemented as a 2:1 mux between C and D controlled by S1.
    check_output_function: assert property (
        @(posedge clk) Y == (S1 ? D : C)
    );

    // A is not used by the implemented output path.
    check_a_ignored: assert property (
        @(posedge clk)
        $changed(A) && $stable(B) && $stable(C) && $stable(D) && $stable(S0) && $stable(S1)
        |-> $stable(Y)
    );

    // B is not used by the implemented output path.
    check_b_ignored: assert property (
        @(posedge clk)
        $changed(B) && $stable(A) && $stable(C) && $stable(D) && $stable(S0) && $stable(S1)
        |-> $stable(Y)
    );

    // S0 does not affect the implemented output path.
    check_s0_ignored: assert property (
        @(posedge clk)
        $changed(S0) && $stable(A) && $stable(B) && $stable(C) && $stable(D) && $stable(S1)
        |-> $stable(Y)
    );

    // C is unselected when S1 is high.
    check_c_ignored_when_s1_high: assert property (
        @(posedge clk)
        S1 && $changed(C) && $stable(A) && $stable(B) && $stable(D) && $stable(S0) && $stable(S1)
        |-> $stable(Y)
    );

    // D is unselected when S1 is low.
    check_d_ignored_when_s1_low: assert property (
        @(posedge clk)
        !S1 && $changed(D) && $stable(A) && $stable(B) && $stable(C) && $stable(S0) && $stable(S1)
        |-> $stable(Y)
    );

endmodule