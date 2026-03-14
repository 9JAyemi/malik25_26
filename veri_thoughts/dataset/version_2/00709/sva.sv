module XOR_sva (
    input  logic        clk,   // sampling clock for combinational checks
    input  logic [7:0]  A,
    input  logic [7:0]  B,
    input  logic [7:0]  C
);
    // C implements (~(A & B)) & (A | B) bitwise.
    check_functional_equation: assert property (
        @(posedge clk) disable iff (1'b0) C === ((~(A & B)) & (A | B))
    );

    // C is equivalent to bitwise XOR of A and B.
    check_xor_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) C === (A ^ B)
    );

    // If inputs are fully known, output must be fully known.
    check_known_inputs_imply_known_output: assert property (
        @(posedge clk) disable iff (1'b0) (!$isunknown({A,B})) |-> (!$isunknown(C))
    );

    // When A equals B, C must be all zeros.
    check_equal_inputs_zero: assert property (
        @(posedge clk) disable iff (1'b0) (A === B) |-> (C === 8'h00)
    );

    // When A is bitwise complement of B, C must be all ones.
    check_complement_inputs_ones: assert property (
        @(posedge clk) disable iff (1'b0) (A === ~B) |-> (C === 8'hFF)
    );

    // XOR identity: A ^ 0 = A -> C equals B when A is zero.
    check_identity_A_zero: assert property (
        @(posedge clk) disable iff (1'b0) (A === 8'h00) |-> (C === B)
    );

    // XOR identity: 0 ^ B = B -> C equals A when B is zero.
    check_identity_B_zero: assert property (
        @(posedge clk) disable iff (1'b0) (B === 8'h00) |-> (C === A)
    );

    // XOR with all ones: A ^ FF = ~A -> C equals ~B when A is all ones.
    check_invert_when_A_ones: assert property (
        @(posedge clk) disable iff (1'b0) (A === 8'hFF) |-> (C === ~B)
    );

    // XOR with all ones: FF ^ B = ~B -> C equals ~A when B is all ones.
    check_invert_when_B_ones: assert property (
        @(posedge clk) disable iff (1'b0) (B === 8'hFF) |-> (C === ~A)
    );

    // Parity consistency: parity(C) equals parity(A) XOR parity(B) when inputs known.
    check_parity_consistency: assert property (
        @(posedge clk) disable iff (1'b0) (!$isunknown({A,B})) |-> ((^C) === ((^A) ^ (^B)))
    );
endmodule