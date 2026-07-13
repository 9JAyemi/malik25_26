module binary_to_gray_sva (
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  G
);
    ///// Bitwise mapping checks /////
    // G[0] must equal A[0].
    check_g0_map: assert property (
        @(posedge clk) G[0] == A[0]
    );
    // G[1] must equal A[0] ^ A[1].
    check_g1_map: assert property (
        @(posedge clk) G[1] == (A[0] ^ A[1])
    );
    // G[2] must equal A[1] ^ A[2].
    check_g2_map: assert property (
        @(posedge clk) G[2] == (A[1] ^ A[2])
    );
    // G[3] must equal A[2] ^ A[3].
    check_g3_map: assert property (
        @(posedge clk) G[3] == (A[2] ^ A[3])
    );
    // G must equal {A2^A3, A1^A2, A0^A1, A0}.
    check_vector_map: assert property (
        @(posedge clk) G == { (A[2]^A[3]), (A[1]^A[2]), (A[0]^A[1]), A[0] }
    );

    ///// Temporal consistency checks /////
    // If A is stable across a cycle, G must be stable.
    check_stability: assert property (
        @(posedge clk) $stable(A) |-> $stable(G)
    );

    ///// Input toggle effect checks /////
    // If only A[0] toggles, G[0] and G[1] toggle; G[2:3] stay stable.
    check_toggle_from_a0: assert property (
        @(posedge clk) ($changed(A[0]) && $stable(A[3:1]))
        |-> ($changed(G[0]) && $changed(G[1]) && $stable(G[3:2]))
    );
    // If only A[1] toggles, G[1] and G[2] toggle; G[0] and G[3] stay stable.
    check_toggle_from_a1: assert property (
        @(posedge clk) ($changed(A[1]) && $stable({A[3:2],A[0]}))
        |-> ($changed(G[1]) && $changed(G[2]) && $stable({G[3],G[0]}))
    );
    // If only A[2] toggles, G[2] and G[3] toggle; G[0] and G[1] stay stable.
    check_toggle_from_a2: assert property (
        @(posedge clk) ($changed(A[2]) && $stable({A[3],A[1:0]}))
        |-> ($changed(G[2]) && $changed(G[3]) && $stable(G[1:0]))
    );
    // If only A[3] toggles, only G[3] toggles; G[0:2] stay stable.
    check_toggle_from_a3: assert property (
        @(posedge clk) ($changed(A[3]) && $stable(A[2:0]))
        |-> ($changed(G[3]) && $stable(G[2:0]))
    );
endmodule