module adder_sva (
    // DUT ports as inputs to the SVA module
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic       C,
    // SVA sampling clock (DUT has no clock/reset; purely combinational)
    input logic       CLK
);
    // Combinational adder: sum = A + B; S = sum[7:0]; C = sum[8].

    // Outputs equal zero-extended sum of inputs.
    check_sum_concat: assert property (
        @(posedge CLK) {C, S} == ({1'b0, A} + {1'b0, B})
    );

    // S equals the lower 8 bits of the sum.
    check_sum_low_bits: assert property (
        @(posedge CLK) S == ({1'b0, A} + {1'b0, B})[7:0]
    );

    // C equals the carry-out bit of the sum.
    check_carry_bit: assert property (
        @(posedge CLK) C == ({1'b0, A} + {1'b0, B})[8]
    );

    // Additive identity when B is zero.
    check_identity_B_zero: assert property (
        @(posedge CLK) (B == 8'h00) |-> ({C, S} == {1'b0, A})
    );

    // Additive identity when A is zero.
    check_identity_A_zero: assert property (
        @(posedge CLK) (A == 8'h00) |-> ({C, S} == {1'b0, B})
    );

    // Increment by one when B is 1.
    check_increment_B_one: assert property (
        @(posedge CLK) (B == 8'h01) |-> ({C, S} == ({1'b0, A} + 9'd1))
    );

    // Increment by one when A is 1.
    check_increment_A_one: assert property (
        @(posedge CLK) (A == 8'h01) |-> ({C, S} == ({1'b0, B} + 9'd1))
    );

    // Max inputs produce 0x1FE (S=0xFE, C=1).
    check_max_plus_max: assert property (
        @(posedge CLK) (A == 8'hFF && B == 8'hFF) |-> (S == 8'hFE && C == 1'b1)
    );

    // If inputs are stable, outputs must be stable (pure combinational).
    check_stability_no_state: assert property (
        @(posedge CLK) $stable({A, B}) |-> $stable({C, S})
    );
endmodule