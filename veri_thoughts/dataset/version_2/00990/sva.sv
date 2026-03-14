module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    ///// Functional correctness (combinational, sampled on clk) /////
    // Outputs equal zero-extended 4-bit sum per LRM sizing of A+B+Cin.
    check_sum_zero_extended: assert property (
        @(posedge clk) disable iff (1'b0) {Cout, S} == (A + B + Cin)
    );
    // S equals 4-bit sum of A, B, and Cin.
    check_sum_low4: assert property (
        @(posedge clk) disable iff (1'b0) S == (A + B + Cin)
    );
    // All-zero inputs produce all-zero outputs.
    check_all_zero_input: assert property (
        @(posedge clk) disable iff (1'b0) (A == 4'b0 && B == 4'b0 && Cin == 1'b0) |-> ({Cout, S} == 5'b0)
    );
    // Adding zero to B with Cin=0 yields S=A and Cout=0.
    check_identity_B0_C0: assert property (
        @(posedge clk) disable iff (1'b0) (B == 4'b0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );
    // Adding zero to A with Cin=0 yields S=B and Cout=0.
    check_identity_A0_C0: assert property (
        @(posedge clk) disable iff (1'b0) (A == 4'b0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );
    // With A,B,Cin stable across cycles, outputs remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(A) && $stable(B) && $stable(Cin) |-> $stable({Cout, S})
    );
    // Swapping A and B across cycles with Cin unchanged leaves outputs unchanged.
    check_commutativity_across_cycles: assert property (
        @(posedge clk) disable iff (1'b0) ($past(Cin) == Cin) && (A == $past(B)) && (B == $past(A)) |-> ({Cout, S} == $past({Cout, S}))
    );
    // With A,B stable, raising Cin increments S modulo 16.
    check_increment_on_cin_rise: assert property (
        @(posedge clk) disable iff (1'b0) $stable(A) && $stable(B) && ($past(Cin) == 1'b0) && (Cin == 1'b1) |-> S == ($past(S) + 4'd1)
    );
    // With A,B stable, lowering Cin decrements S modulo 16.
    check_decrement_on_cin_fall: assert property (
        @(posedge clk) disable iff (1'b0) $stable(A) && $stable(B) && ($past(Cin) == 1'b1) && (Cin == 1'b0) |-> S == ($past(S) - 4'd1)
    );
    // LSB of S is XOR of input LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) disable iff (1'b0) S[0] == (A[0] ^ B[0] ^ Cin)
    );
endmodule