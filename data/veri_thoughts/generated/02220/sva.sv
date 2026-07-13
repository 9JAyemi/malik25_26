module binary_to_excess3_sva (
    input  logic       CLK,  // Sampling clock for assertions (DUT has no clock/reset)
    input  logic [3:0] B,
    input  logic [3:0] E
);
    ///// Functional mapping /////
    // E must equal B + 3 modulo 16.
    check_ex3_mapping: assert property (
        @(posedge CLK) E == (B + 4'd3)[3:0]
    );

    ///// Key specific mappings (including wrap-around cases) /////
    // B=0 maps to E=3.
    check_map_b0: assert property (
        @(posedge CLK) (B == 4'b0000) |-> (E == 4'b0011)
    );
    // B=9 maps to E=12.
    check_map_b9: assert property (
        @(posedge CLK) (B == 4'b1001) |-> (E == 4'b1100)
    );
    // B=12 maps to E=15.
    check_map_b12: assert property (
        @(posedge CLK) (B == 4'b1100) |-> (E == 4'b1111)
    );
    // B=13 wraps to E=0.
    check_map_wrap_b13: assert property (
        @(posedge CLK) (B == 4'b1101) |-> (E == 4'b0000)
    );
    // B=14 wraps to E=1.
    check_map_wrap_b14: assert property (
        @(posedge CLK) (B == 4'b1110) |-> (E == 4'b0001)
    );
    // B=15 wraps to E=2.
    check_map_wrap_b15: assert property (
        @(posedge CLK) (B == 4'b1111) |-> (E == 4'b0010)
    );

    ///// Temporal consistency (pure combinational behavior) /////
    // If B is stable across a cycle, E must be stable.
    check_stable_when_B_stable: assert property (
        @(posedge CLK) $stable(B) |-> $stable(E)
    );
    // If B changes across a cycle, E must change (bijection).
    check_E_changes_when_B_changes: assert property (
        @(posedge CLK) !$stable(B) |-> !$stable(E)
    );
    // If B increments by 1 modulo 16, E increments by 1 modulo 16.
    check_increment_consistency: assert property (
        @(posedge CLK) (B == ($past(B) + 4'd1)[3:0]) |-> (E == ($past(E) + 4'd1)[3:0])
    );
endmodule