module ripple_adder_64_sva (
    input logic clk,
    input logic [63:0] A,
    input logic [63:0] B,
    input logic [63:0] SUM,
    input logic CARRY
);

    // Full output must equal the 65-bit sum of A and B.
    check_total_sum: assert property (
        @(posedge clk) {CARRY, SUM} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 sum is A[0] xor B[0] because the initial carry-in is tied low.
    check_lsb_xor: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0])
    );

    // Zero plus zero produces zero with no carry-out.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((A == 64'h0000_0000_0000_0000) && (B == 64'h0000_0000_0000_0000)) |->
                       ((SUM == 64'h0000_0000_0000_0000) && (CARRY == 1'b0))
    );

    // A equal to zero passes B through with no carry-out.
    check_a_zero_passthrough: assert property (
        @(posedge clk) (A == 64'h0000_0000_0000_0000) |->
                       ((SUM == B) && (CARRY == 1'b0))
    );

    // B equal to zero passes A through with no carry-out.
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 64'h0000_0000_0000_0000) |->
                       ((SUM == A) && (CARRY == 1'b0))
    );

    // Disjoint set bits add without generating any carry.
    check_disjoint_bits_no_carry: assert property (
        @(posedge clk) ((A & B) == 64'h0000_0000_0000_0000) |->
                       ((SUM == (A | B)) && (CARRY == 1'b0))
    );

    // Complementary inputs sum to all ones with no carry-out.
    check_complementary_inputs: assert property (
        @(posedge clk) (A == ~B) |->
                       ((SUM == 64'hFFFF_FFFF_FFFF_FFFF) && (CARRY == 1'b0))
    );

    // All ones plus one wraps the sum and raises carry-out.
    check_max_plus_one: assert property (
        @(posedge clk) ((A == 64'hFFFF_FFFF_FFFF_FFFF) && (B == 64'h0000_0000_0000_0001)) |->
                       ((SUM == 64'h0000_0000_0000_0000) && (CARRY == 1'b1))
    );

    // All ones plus all ones produces FFFE with carry-out asserted.
    check_max_plus_max: assert property (
        @(posedge clk) ((A == 64'hFFFF_FFFF_FFFF_FFFF) && (B == 64'hFFFF_FFFF_FFFF_FFFF)) |->
                       ((SUM == 64'hFFFF_FFFF_FFFF_FFFE) && (CARRY == 1'b1))
    );

    // Any nonzero addend combined with all ones on A must overflow.
    check_all_ones_a_overflow: assert property (
        @(posedge clk) ((A == 64'hFFFF_FFFF_FFFF_FFFF) && (B != 64'h0000_0000_0000_0000)) |->
                       (CARRY == 1'b1)
    );

    // Any nonzero addend combined with all ones on B must overflow.
    check_all_ones_b_overflow: assert property (
        @(posedge clk) ((B == 64'hFFFF_FFFF_FFFF_FFFF) && (A != 64'h0000_0000_0000_0000)) |->
                       (CARRY == 1'b1)
    );

endmodule