module buffer3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic EN,
    input logic Z
);
    // When EN is HIGH, Z must equal A.
    check_en_selects_a: assert property (
        @(posedge clk) EN |-> (Z == A)
    );

    // When EN is LOW and B is HIGH, Z must be 1.
    check_b_forces_one_when_en0: assert property (
        @(posedge clk) (!EN && (B == 1'b1)) |-> (Z == 1'b1)
    );

    // When EN is LOW and B is LOW, Z must equal C.
    check_c_selected_when_en0_b0: assert property (
        @(posedge clk) (!EN && (B == 1'b0)) |-> (Z == C)
    );

    // Z can only change if at least one input (A,B,C,EN) changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(Z) |-> $changed({A,B,C,EN})
    );

    // If all inputs are stable, Z must remain stable.
    check_inputs_stable_keep_output_stable: assert property (
        @(posedge clk) $stable({A,B,C,EN}) |-> $stable(Z)
    );

    // With EN HIGH and stable, a change on A must change Z.
    check_en1_a_change_updates_z: assert property (
        @(posedge clk) (EN && $stable(EN) && $changed(A)) |-> $changed(Z)
    );

    // With EN HIGH and A stable, a change on B must not change Z.
    check_en1_b_change_not_affect_z: assert property (
        @(posedge clk) (EN && $stable(EN) && $stable(A) && $changed(B)) |-> $stable(Z)
    );

    // With EN HIGH and A stable, a change on C must not change Z.
    check_en1_c_change_not_affect_z: assert property (
        @(posedge clk) (EN && $stable(EN) && $stable(A) && $changed(C)) |-> $stable(Z)
    );

    // With EN LOW and B LOW (both stable), a change on C must change Z.
    check_en0_b0_c_change_updates_z: assert property (
        @(posedge clk) (!EN && $stable(EN) && (B == 1'b0) && $stable(B) && $changed(C)) |-> $changed(Z)
    );

    // With EN LOW and B HIGH (both stable), a change on A must not change Z.
    check_en0_b1_a_change_not_affect_z: assert property (
        @(posedge clk) (!EN && $stable(EN) && (B == 1'b1) && $stable(B) && $changed(A)) |-> $stable(Z)
    );

    // With EN LOW and B HIGH (both stable), a change on C must not change Z.
    check_en0_b1_c_change_not_affect_z: assert property (
        @(posedge clk) (!EN && $stable(EN) && (B == 1'b1) && $stable(B) && $changed(C)) |-> $stable(Z)
    );
endmodule