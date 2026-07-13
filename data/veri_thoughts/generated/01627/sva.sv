module sky130_fd_sc_hdll__xnor2_sva (
    input logic Y,
    input logic A,
    input logic B
);
    // No clock/reset in RTL; pure combinational XNOR; sample on any edge of A or B.

    // Y implements XNOR of A and B.
    check_xnor_function: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (Y === (A ~^ B))
    );

    // If B==1, Y follows A.
    check_b_one_transparent: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (B == 1'b1) |-> (Y === A)
    );

    // If B==0, Y equals ~A.
    check_b_zero_inverts: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (B == 1'b0) |-> (Y === ~A)
    );

    // If A==1, Y follows B.
    check_a_one_transparent: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A == 1'b1) |-> (Y === B)
    );

    // If A==0, Y equals ~B.
    check_a_zero_inverts: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A == 1'b0) |-> (Y === ~B)
    );

    // When A and B are known equal, Y is 1.
    check_equal_inputs_imply_one: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A == B) |-> (Y === 1'b1)
    );

    // When A and B are known different, Y is 0.
    check_diff_inputs_imply_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A != B) |-> (Y === 1'b0)
    );

    // Y is never high-impedance.
    check_y_never_z: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (Y !== 1'bz)
    );

    // If only A toggles and B is stable (both known), Y toggles.
    check_toggle_on_A_only: assert property (
        @(posedge A or negedge A or posedge B or negedge B)
        ((A == ~$past(A)) && (B == $past(B))) |-> (Y == ~$past(Y))
    );

    // If only B toggles and A is stable (both known), Y toggles.
    check_toggle_on_B_only: assert property (
        @(posedge A or negedge A or posedge B or negedge B)
        ((B == ~$past(B)) && (A == $past(A))) |-> (Y == ~$past(Y))
    );

    // If both A and B toggle (both known), Y holds its value.
    check_both_toggle_hold: assert property (
        @(posedge A or negedge A or posedge B or negedge B)
        ((A == ~$past(A)) && (B == ~$past(B))) |-> (Y == $past(Y))
    );

endmodule