module jcarryskipadder_sva (
    input logic [7:0] Y,
    input logic       carryout,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       carryin
);

    // Whole combinational adder matches 8-bit addition with carry.
    check_full_sum: assert property (
        @($global_clock) {carryout, Y} == ({1'b0, A} + {1'b0, B} + carryin)
    );

    // The low nibble matches the first 4-bit block sum.
    check_low_nibble_sum: assert property (
        @($global_clock) Y[3:0] == (A[3:0] + B[3:0] + carryin)
    );

    // The least-significant sum bit uses the incoming carry.
    check_bit0_sum: assert property (
        @($global_clock) Y[0] == (A[0] ^ B[0] ^ carryin)
    );

    // A fully propagating low nibble passes carryin into bit 4.
    check_low_block_skip_to_bit4: assert property (
        @($global_clock) ((A[3:0] ^ B[3:0]) == 4'hF) |-> (Y[4] == (A[4] ^ B[4] ^ carryin))
    );

    // A fully propagating low nibble inverts carryin on all low sum bits.
    check_low_block_propagate_sum: assert property (
        @($global_clock) ((A[3:0] ^ B[3:0]) == 4'hF) |-> (Y[3:0] == {4{~carryin}})
    );

    // A fully propagating byte passes carryin through to carryout.
    check_full_propagate_carryout: assert property (
        @($global_clock) ((A ^ B) == 8'hFF) |-> (carryout == carryin)
    );

    // A fully propagating byte inverts carryin on all sum bits.
    check_full_propagate_sum: assert property (
        @($global_clock) ((A ^ B) == 8'hFF) |-> (Y == {8{~carryin}})
    );

endmodule