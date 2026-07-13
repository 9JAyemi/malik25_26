module xnor4_sva (
    input logic clk,
    input logic reset_n,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);
    // Y equals NOR-reduction of bitwise XOR across A,B,C,D.
    check_y_function: assert property (
        @(posedge clk) disable iff (!reset_n) Y == ~(|(((A ^ B) ^ (C ^ D))))
    );

    // If (A^B) equals (C^D), Y must be 1.
    check_y_true_when_xor_vectors_equal: assert property (
        @(posedge clk) disable iff (!reset_n) (((A ^ B) == (C ^ D))) |-> (Y == 1'b1)
    );

    // If (A^B) differs from (C^D), Y must be 0.
    check_y_false_when_xor_vectors_different: assert property (
        @(posedge clk) disable iff (!reset_n) (((A ^ B) != (C ^ D))) |-> (Y == 1'b0)
    );

    // Y is unaffected when only VPWR changes and data inputs are stable.
    check_y_stable_on_vpwr_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($stable(A) && $stable(B) && $stable(C) && $stable(D) && $changed(VPWR)) |-> $stable(Y)
    );

    // Y is unaffected when only VGND changes and data inputs are stable.
    check_y_stable_on_vgnd_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($stable(A) && $stable(B) && $stable(C) && $stable(D) && $changed(VGND)) |-> $stable(Y)
    );

    // Y is unaffected when only VPB changes and data inputs are stable.
    check_y_stable_on_vpb_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($stable(A) && $stable(B) && $stable(C) && $stable(D) && $changed(VPB)) |-> $stable(Y)
    );

    // Y is unaffected when only VNB changes and data inputs are stable.
    check_y_stable_on_vnb_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        ($stable(A) && $stable(B) && $stable(C) && $stable(D) && $changed(VNB)) |-> $stable(Y)
    );

    // Swapping A and B leaves Y unchanged (with C,D held).
    check_y_invariant_under_swap_ab: assert property (
        @(posedge clk) disable iff (!reset_n)
        (A == $past(B) && B == $past(A) && C == $past(C) && D == $past(D)) |-> (Y == $past(Y))
    );

    // Swapping C and D leaves Y unchanged (with A,B held).
    check_y_invariant_under_swap_cd: assert property (
        @(posedge clk) disable iff (!reset_n)
        (A == $past(A) && B == $past(B) && C == $past(D) && D == $past(C)) |-> (Y == $past(Y))
    );

    // If ((A^B)^(C^D)) is stable, Y must be stable.
    check_y_stable_when_xor_input_stable: assert property (
        @(posedge clk) disable iff (!reset_n)
        $stable(((A ^ B) ^ (C ^ D))) |-> $stable(Y)
    );

    // Y changes only if ((A^B)^(C^D)) changes.
    check_y_change_requires_xor_input_change: assert property (
        @(posedge clk) disable iff (!reset_n)
        $changed(Y) |-> $changed(((A ^ B) ^ (C ^ D)))
    );

    // If A==B and C==D, then Y must be 1.
    check_y_one_when_pairs_equal: assert property (
        @(posedge clk) disable iff (!reset_n) ((A == B) && (C == D)) |-> (Y == 1'b1)
    );

    // If A==B and C!=D, then Y must be 0.
    check_y_zero_when_cd_diff_only: assert property (
        @(posedge clk) disable iff (!reset_n) ((A == B) && (C != D)) |-> (Y == 1'b0)
    );

    // If A!=B and C==D, then Y must be 0.
    check_y_zero_when_ab_diff_only: assert property (
        @(posedge clk) disable iff (!reset_n) ((A != B) && (C == D)) |-> (Y == 1'b0)
    );
endmodule