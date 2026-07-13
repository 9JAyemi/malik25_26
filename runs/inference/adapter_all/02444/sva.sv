module my_buffer_sva (
    input logic A,
    input logic Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // Z equals A gated by TE_B.
    check_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        Z == (TE_B ? A : 1'b0)
    );

    // When TE_B is LOW, Z must be LOW.
    check_te_b_low_forces_z_low: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b0) |-> (Z == 1'b0)
    );

    // When TE_B is HIGH, Z equals A.
    check_te_b_high_passes_a: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b1) |-> (Z == A)
    );

    // If A and TE_B are stable, Z must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        ($stable(A) && $stable(TE_B)) |-> $stable(Z)
    );

    // If Z changes, at least one of A or TE_B must have changed.
    check_z_change_has_cause: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        $changed(Z) |-> ($changed(A) || $changed(TE_B))
    );

    // With TE_B HIGH and A rising, Z must rise.
    check_te_b_high_a_rise_propagates: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b1 && $rose(A)) |-> $rose(Z)
    );

    // With TE_B HIGH and A falling, Z must fall.
    check_te_b_high_a_fall_propagates: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b1 && $fell(A)) |-> $fell(Z)
    );

    // With TE_B LOW and A rising, Z must stay LOW.
    check_te_b_low_a_rise_blocks: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b0 && $rose(A)) |-> $stable(Z)
    );

    // With TE_B LOW and A falling, Z must stay LOW.
    check_te_b_low_a_fall_blocks: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b0 && $fell(A)) |-> $stable(Z)
    );

    // With TE_B HIGH and Z rising, A must be HIGH.
    check_te_b_high_z_rise_requires_a_high: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b1 && $rose(Z)) |-> (A == 1'b1)
    );

    // With TE_B HIGH and Z falling, A must be LOW.
    check_te_b_high_z_fall_requires_a_low: assert property (
        @(posedge A or negedge A or posedge TE_B or negedge TE_B or posedge Z or negedge Z)
        (TE_B == 1'b1 && $fell(Z)) |-> (A == 1'b0)
    );
endmodule