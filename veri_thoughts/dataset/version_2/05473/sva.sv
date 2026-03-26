module adder4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic       CK,
    input logic [3:0] S,
    input logic       Cout
);

    // CK is the only clock and the RTL has no reset.

    // Outputs equal the previous cycle's 5-bit sum.
    check_registered_sum: assert property (
        @(posedge CK) 1'b1 |=> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)))
    );

    // Sum bits match the low 4 bits of the previous addition.
    check_sum_bits_match: assert property (
        @(posedge CK) 1'b1 |=> ({1'b0, S} == (({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)) & 5'h0F))
    );

    // Carry-out matches overflow from the previous addition.
    check_carry_bit_match: assert property (
        @(posedge CK) 1'b1 |=> (Cout == (({1'b0, $past(A)} + {1'b0, $past(B)} + $past(Cin)) > 5'h0F))
    );

    // Stable inputs across cycles keep the registered output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge CK) $stable({A, B, Cin}) |=> $stable({Cout, S})
    );

    // All-zero inputs produce an all-zero registered result.
    check_zero_inputs_produce_zero: assert property (
        @(posedge CK) (A == 4'h0 && B == 4'h0 && Cin == 1'b0) |=> ({Cout, S} == 5'h00)
    );

    // Maximum inputs produce the full-scale registered result.
    check_max_inputs_produce_full_scale: assert property (
        @(posedge CK) (A == 4'hF && B == 4'hF && Cin == 1'b1) |=> ({Cout, S} == 5'h1F)
    );

    // With B and Cin zero, the registered result passes A through.
    check_pass_through_a_when_b_and_cin_zero: assert property (
        @(posedge CK) (B == 4'h0 && Cin == 1'b0) |=> ({Cout, S} == {1'b0, $past(A)})
    );

    // With A and Cin zero, the registered result passes B through.
    check_pass_through_b_when_a_and_cin_zero: assert property (
        @(posedge CK) (A == 4'h0 && Cin == 1'b0) |=> ({Cout, S} == {1'b0, $past(B)})
    );

endmodule