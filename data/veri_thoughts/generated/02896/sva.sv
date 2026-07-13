module sky130_fd_sc_ms__or4_sva (
    input  logic clk,  // assertion clock (no clock/reset in DUT)
    input  logic X,
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic D
);
    // Analysis: no clock/reset in DUT; pure combinational; X = A | B | C | D.

    // X equals the bitwise OR of A,B,C,D every cycle.
    check_x_equals_or: assert property (
        @(posedge clk) X === (A | B | C | D)
    );

    // All inputs 0 implies X is 0.
    check_all_zero_implies_x_zero: assert property (
        @(posedge clk) (A === 1'b0 && B === 1'b0 && C === 1'b0 && D === 1'b0) |-> (X === 1'b0)
    );

    // A=1 drives X=1.
    check_a_one_implies_x_one: assert property (
        @(posedge clk) (A === 1'b1) |-> (X === 1'b1)
    );

    // B=1 drives X=1.
    check_b_one_implies_x_one: assert property (
        @(posedge clk) (B === 1'b1) |-> (X === 1'b1)
    );

    // C=1 drives X=1.
    check_c_one_implies_x_one: assert property (
        @(posedge clk) (C === 1'b1) |-> (X === 1'b1)
    );

    // D=1 drives X=1.
    check_d_one_implies_x_one: assert property (
        @(posedge clk) (D === 1'b1) |-> (X === 1'b1)
    );

    // X=0 implies all inputs are 0.
    check_x_zero_implies_all_zero: assert property (
        @(posedge clk) (X === 1'b0) |-> (A === 1'b0 && B === 1'b0 && C === 1'b0 && D === 1'b0)
    );

    // X=1 implies at least one input is 1.
    check_x_one_implies_any_one: assert property (
        @(posedge clk) (X === 1'b1) |-> (A === 1'b1 || B === 1'b1 || C === 1'b1 || D === 1'b1)
    );

    // If inputs are stable across a cycle, X is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,C,D}) |-> $stable(X)
    );

endmodule