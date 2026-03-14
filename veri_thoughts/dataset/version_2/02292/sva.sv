module ripple_carry_adder_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);
    // No clock or reset in DUT; purely combinational.
    // Sample assertions on posedges of existing inputs.

    // Local combinational carry expressions derived from DUT ports.
    let c0e = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);
    let c1e = (a[1] & b[1]) | (a[1] & c0e) | (b[1] & c0e);
    let c2e = (a[2] & b[2]) | (a[2] & c1e) | (b[2] & c1e);
    let c3e = (a[3] & b[3]) | (a[3] & c2e) | (b[3] & c2e);

    ///// Functional equivalence /////
    // Full 4-bit add with carry-in matches outputs (sample on cin).
    check_adder_equivalence_on_cin: assert property (
        @(posedge cin) {cout, sum} == (a + b + cin)[4:0]
    );
    // Full 4-bit add with carry-in matches outputs (sample on a[0]).
    check_adder_equivalence_on_a0: assert property (
        @(posedge a[0]) {cout, sum} == (a + b + cin)[4:0]
    );
    // Full 4-bit add with carry-in matches outputs (sample on b[0]).
    check_adder_equivalence_on_b0: assert property (
        @(posedge b[0]) {cout, sum} == (a + b + cin)[4:0]
    );

    ///// Bit-level relationships /////
    // LSB sum is XOR of a[0], b[0], and cin.
    check_sum0_xor: assert property (
        @(posedge cin) sum[0] == (a[0] ^ b[0] ^ cin)
    );
    // sum[1] uses carry from bit 0.
    check_sum1_xor: assert property (
        @(posedge cin) sum[1] == (a[1] ^ b[1] ^ c0e)
    );
    // sum[2] uses carry from bit 1.
    check_sum2_xor: assert property (
        @(posedge cin) sum[2] == (a[2] ^ b[2] ^ c1e)
    );
    // sum[3] uses carry from bit 2.
    check_sum3_xor: assert property (
        @(posedge cin) sum[3] == (a[3] ^ b[3] ^ c2e)
    );
    // Top-level carry-out equals carry from bit 3.
    check_cout_matches_c3: assert property (
        @(posedge cin) cout == c3e
    );

    ///// Corner-case identities /////
    // Adding all zeros yields zero sum and zero carry.
    check_zero_identity: assert property (
        @(posedge cin) (a == 4'd0 && b == 4'd0 && cin == 1'b0) |-> (sum == 4'd0 && cout == 1'b0)
    );
    // 0 + 0 + 1 yields sum=1 and no carry.
    check_plus_one_identity: assert property (
        @(posedge cin) (a == 4'd0 && b == 4'd0 && cin == 1'b1) |-> (sum == 4'd1 && cout == 1'b0)
    );
endmodule