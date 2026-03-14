module DFF_RST_SET_sva (
    input logic D,
    input logic C,
    input logic R,
    input logic S,
    input logic Q
);
    // Clock: C; Active-high reset-like control: R; Combinational: Q = (R?0 : S?1 : D)

    // Reset forces Q to 0 regardless of S or D.
    check_reset_forces_zero: assert property (
        @(posedge C) R |-> (Q == 1'b0)
    );

    // When not reset, Q implements priority set/through function (S over D).
    check_function_when_not_reset: assert property (
        @(posedge C) disable iff (R) (Q == (S ? 1'b1 : D))
    );

    // When not reset and S is high, Q must be 1 independent of D.
    check_set_when_not_reset: assert property (
        @(posedge C) disable iff (R) S |-> (Q == 1'b1)
    );

    // When not reset and S is low, Q must equal D.
    check_pass_through_when_not_reset: assert property (
        @(posedge C) disable iff (R) (!S) |-> (Q == D)
    );

    // If both R and S are high, R has priority and Q is 0.
    check_priority_R_over_S: assert property (
        @(posedge C) (R && S) |-> (Q == 1'b0)
    );
endmodule