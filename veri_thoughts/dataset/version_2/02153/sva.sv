module adder_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);
    // Sum output must equal the RTL expression A + B + CIN (concatenated with COUT).
    check_sum_matches_rtl: assert property (
        @(posedge CLK) {COUT, S} == (A + B + CIN)
    );

    // S must equal the low 4 bits of A + B + CIN per RTL.
    check_s_lower_bits: assert property (
        @(posedge CLK) S == (A + B + CIN)
    );

    // If inputs are stable between samples, outputs must also be stable.
    check_stable_inputs_imply_stable_outputs: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(CIN)) |-> $stable({COUT, S})
    );

    // Swapping A and B between cycles with CIN unchanged leaves outputs unchanged (commutativity).
    check_commutativity_across_cycles: assert property (
        @(posedge CLK) (A == $past(B)) && (B == $past(A)) && (CIN == $past(CIN)) |-> ({COUT, S} == $past({COUT, S}))
    );

    // If B and CIN are zero, output equals A with no carry (per RTL expression).
    check_identity_with_B_zero_CIN_zero: assert property (
        @(posedge CLK) (B == 4'b0000) && (CIN == 1'b0) |-> ({COUT, S} == {1'b0, A})
    );

    // If A and CIN are zero, output equals B with no carry (per RTL expression).
    check_identity_with_A_zero_CIN_zero: assert property (
        @(posedge CLK) (A == 4'b0000) && (CIN == 1'b0) |-> ({COUT, S} == {1'b0, B})
    );

    // If A and B are zero, S equals CIN in bit[0] and COUT is zero (per RTL expression).
    check_zero_plus_zero: assert property (
        @(posedge CLK) (A == 4'b0000) && (B == 4'b0000) |-> (S == {3'b000, CIN}) && (COUT == 1'b0)
    );
endmodule