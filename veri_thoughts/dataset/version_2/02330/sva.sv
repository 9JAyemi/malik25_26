module gray_code_sva (
    input logic CLK,
    input logic [3:0] D,
    input logic [3:0] G
);
    // G must equal the Gray encoding of D
    check_gray_encode_vector: assert property (
        @(posedge CLK) G == {D[3], (D[3]^D[2]), (D[2]^D[1]), (D[1]^D[0])}
    );

    // If only D[0] toggles between cycles, only G[0] toggles.
    check_toggle_from_d0: assert property (
        @(posedge CLK) ((D ^ $past(D)) == 4'b0001) |-> ((G ^ $past(G)) == 4'b0001)
    );

    // If only D[1] toggles between cycles, only G[1] and G[0] toggle.
    check_toggle_from_d1: assert property (
        @(posedge CLK) ((D ^ $past(D)) == 4'b0010) |-> ((G ^ $past(G)) == 4'b0011)
    );

    // If only D[2] toggles between cycles, only G[2] and G[1] toggle.
    check_toggle_from_d2: assert property (
        @(posedge CLK) ((D ^ $past(D)) == 4'b0100) |-> ((G ^ $past(G)) == 4'b0110)
    );

    // If only D[3] toggles between cycles, only G[3] and G[2] toggle.
    check_toggle_from_d3: assert property (
        @(posedge CLK) ((D ^ $past(D)) == 4'b1000) |-> ((G ^ $past(G)) == 4'b1100)
    );

    // If D is stable across cycles, G must be stable.
    check_stability_when_D_stable: assert property (
        @(posedge CLK) $stable(D) |-> $stable(G)
    );

    // G[3] can change only if D[3] changes.
    check_g3_changes_only_with_d3: assert property (
        @(posedge CLK) $changed(G[3]) |-> $changed(D[3])
    );

    // G[2] can change only if D[3] or D[2] changes.
    check_g2_changes_only_with_d3_or_d2: assert property (
        @(posedge CLK) $changed(G[2]) |-> ($changed(D[3]) || $changed(D[2]))
    );

    // G[1] can change only if D[2] or D[1] changes.
    check_g1_changes_only_with_d2_or_d1: assert property (
        @(posedge CLK) $changed(G[1]) |-> ($changed(D[2]) || $changed(D[1]))
    );

    // G[0] can change only if D[1] or D[0] changes.
    check_g0_changes_only_with_d1_or_d0: assert property (
        @(posedge CLK) $changed(G[0]) |-> ($changed(D[1]) || $changed(D[0]))
    );
endmodule