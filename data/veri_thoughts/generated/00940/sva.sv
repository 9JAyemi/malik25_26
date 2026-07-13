module top_module_sva (
    input logic CLK,
    input logic [2:0] A,
    input logic [3:0] in,
    input logic [7:0] q
);
    // q equals onehot(A) OR (in[3] ? onehot(in[2:0]) : 0)
    check_q_matches_formula: assert property (
        @(posedge CLK)
        q == ((8'b00000001 << A) | (in[3] ? (8'b00000001 << in[2:0]) : 8'b00000000))
    );

    // q must always have bit A set
    check_q_bit_A_always_set: assert property (
        @(posedge CLK)
        q[A] == 1'b1
    );

    // When in[3]==0, q is exactly onehot(A)
    check_when_in_msb0_exact: assert property (
        @(posedge CLK)
        (in[3] == 1'b0) |-> (q == (8'b00000001 << A))
    );

    // When in[3]==1, q must include bit indexed by in[2:0]
    check_when_in_msb1_bit_set: assert property (
        @(posedge CLK)
        (in[3] == 1'b1) |-> (q[in[2:0]] == 1'b1)
    );

    // When in[3]==1 and in[2:0]!=A, q has exactly two 1s
    check_two_bits_when_distinct: assert property (
        @(posedge CLK)
        (in[3] && (in[2:0] != A)) |-> ($countones(q) == 2)
    );

    // When in[3]==1 and in[2:0]==A, q is onehot
    check_onehot_when_same: assert property (
        @(posedge CLK)
        (in[3] && (in[2:0] == A)) |-> $onehot(q)
    );

    // q always has one or two 1s
    check_countones_bound: assert property (
        @(posedge CLK)
        ($countones(q) >= 1) && ($countones(q) <= 2)
    );

    // q is never all zeros
    check_q_never_zero: assert property (
        @(posedge CLK)
        q != 8'b00000000
    );

    // No spurious bits in q beyond the two allowed sources
    check_no_spurious_bits: assert property (
        @(posedge CLK)
        (q & ~((8'b00000001 << A) | (in[3] ? (8'b00000001 << in[2:0]) : 8'b00000000))) == 8'b00000000
    );

    // When in[3]==1, q equals onehot(A) OR onehot(in[2:0])
    check_when_in_msb1_exact: assert property (
        @(posedge CLK)
        (in[3] == 1'b1) |-> (q == ((8'b00000001 << A) | (8'b00000001 << in[2:0])))
    );
endmodule