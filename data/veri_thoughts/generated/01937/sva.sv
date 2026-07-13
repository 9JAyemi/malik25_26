module adder4_sva #(parameter WIDTH = 4) (
    input logic clk,                 // Sampling clock for assertions (RTL is combinational)
    input logic [WIDTH-1:0] A,
    input logic [WIDTH-1:0] B,
    input logic Cin,
    input logic [WIDTH-1:0] S,
    input logic Cout
);
    ///// Functional equivalence to addition /////
    // {Cout,S} must equal A + B + Cin (properly sized).
    check_sum_matches_addition: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // S must match the lower WIDTH bits of A + B + Cin.
    check_s_lower_bits_of_sum: assert property (
        @(posedge clk) S == (({1'b0, A} + {1'b0, B} + Cin)[WIDTH-1:0])
    );

    // Cout must equal the carry-out bit of A + B + Cin.
    check_cout_is_carry_out_of_sum: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[WIDTH])
    );

    ///// Bit-0 behavior /////
    // LSB sum is XOR of A[0], B[0], and Cin.
    check_lsb_sum_logic: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    ///// Simple corner cases /////
    // If A=0 and B=0, then S equals Cin in bit0 and zeros elsewhere; Cout=0.
    check_zero_plus_zero_case: assert property (
        @(posedge clk) ((A == {WIDTH{1'b0}}) && (B == {WIDTH{1'b0}})) |-> 
                       ((S == {{(WIDTH-1){1'b0}}, Cin}) && (Cout == 1'b0))
    );

    // Adding zero B with Cin=0 passes A through and Cout=0.
    check_add_zero_B_no_cin: assert property (
        @(posedge clk) ((B == {WIDTH{1'b0}}) && (Cin == 1'b0)) |-> 
                       ((S == A) && (Cout == 1'b0))
    );

    // Adding zero A with Cin=0 passes B through and Cout=0.
    check_add_zero_A_no_cin: assert property (
        @(posedge clk) ((A == {WIDTH{1'b0}}) && (Cin == 1'b0)) |-> 
                       ((S == B) && (Cout == 1'b0))
    );

    // Complementary operands with Cin=0 produce all-ones sum and no carry.
    check_complements_no_carry: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b0)) |-> 
                       ((S == {WIDTH{1'b1}}) && (Cout == 1'b0))
    );

    // Complementary operands with Cin=1 produce zero sum and carry=1.
    check_complements_with_carry: assert property (
        @(posedge clk) ((B == ~A) && (Cin == 1'b1)) |-> 
                       ((S == {WIDTH{1'b0}}) && (Cout == 1'b1))
    );

    // All-ones plus all-ones with Cin=1 yields S=all-ones and Cout=1.
    check_all_ones_plus_all_ones_cin1: assert property (
        @(posedge clk) ((A == {WIDTH{1'b1}}) && (B == {WIDTH{1'b1}}) && (Cin == 1'b1)) |-> 
                       ((S == {WIDTH{1'b1}}) && (Cout == 1'b1))
    );

    ///// Stability (combinational behavior) /////
    // If inputs are stable across a cycle, outputs must be stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(Cin)) |-> ($stable(S) && $stable(Cout))
    );

    // If LSB inputs are stable across a cycle, S[0] must be stable.
    check_lsb_stable_when_lsb_inputs_stable: assert property (
        @(posedge clk) ($stable(A[0]) && $stable(B[0]) && $stable(Cin)) |-> $stable(S[0])
    );
endmodule