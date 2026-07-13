module XOR4_sva #(
    parameter logic [3:0] B = 4'b0001
) (
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  Z
);
    ///// Functional correctness /////
    // Z must equal A XOR B every cycle.
    check_z_eq_a_xor_b: assert property (
        @(posedge clk) (Z === (A ^ B))
    );
    // Re-applying XOR with B to Z must recover A.
    check_unxor_back_to_a: assert property (
        @(posedge clk) ((Z ^ B) === A)
    );
    // The XOR difference between A and Z must equal B.
    check_a_xor_z_is_b: assert property (
        @(posedge clk) ((A ^ Z) === B)
    );

    ///// Bit-level mapping /////
    // LSB must be inverted due to B[0]==1.
    check_lsb_inverted: assert property (
        @(posedge clk) (Z[0] === ~A[0])
    );
    // Upper bits must pass through due to B[3:1]==0.
    check_upper_pass_through: assert property (
        @(posedge clk) (Z[3:1] === A[3:1])
    );

    ///// Change/stability relationships /////
    // If A is stable over a cycle, Z must be stable.
    check_stability_propagation: assert property (
        @(posedge clk) $stable(A) |-> $stable(Z)
    );
    // Z cannot change unless A changes.
    check_no_spurious_z_change: assert property (
        @(posedge clk) $changed(Z) |-> $changed(A)
    );
    // The per-bit toggle pattern of Z matches that of A.
    check_toggle_pattern_matches: assert property (
        @(posedge clk) $past(1'b1) |-> ((Z ^ $past(Z)) === (A ^ $past(A)))
    );

    ///// Edge correspondence per bit /////
    // For pass-through bits, rising edge on A implies rising edge on Z.
    check_upper_rose_maps:
    assert property (@(posedge clk) $rose(A[3]) |-> $rose(Z[3]));
    check_upper_rose_maps_2:
    assert property (@(posedge clk) $rose(A[2]) |-> $rose(Z[2]));
    check_upper_rose_maps_1:
    assert property (@(posedge clk) $rose(A[1]) |-> $rose(Z[1]));
    // For pass-through bits, falling edge on A implies falling edge on Z.
    check_upper_fell_maps:
    assert property (@(posedge clk) $fell(A[3]) |-> $fell(Z[3]));
    check_upper_fell_maps_2:
    assert property (@(posedge clk) $fell(A[2]) |-> $fell(Z[2]));
    check_upper_fell_maps_1:
    assert property (@(posedge clk) $fell(A[1]) |-> $fell(Z[1]));
    // For inverted bit, rising edge on A implies falling edge on Z.
    check_lsb_rose_inverts: assert property (
        @(posedge clk) $rose(A[0]) |-> $fell(Z[0])
    );
    // For inverted bit, falling edge on A implies rising edge on Z.
    check_lsb_fell_inverts: assert property (
        @(posedge clk) $fell(A[0]) |-> $rose(Z[0])
    );
endmodule