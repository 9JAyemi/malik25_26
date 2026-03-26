module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // No clock or reset exists in the RTL; sample combinational behavior on clk.

    // Sum[0] matches the implemented XOR with Cin.
    check_sum_bit0_logic: assert property (
        @(posedge clk) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] matches the implemented XOR with bit-0 AND.
    check_sum_bit1_logic: assert property (
        @(posedge clk) Sum[1] == (A[1] ^ B[1] ^ (A[0] & B[0]))
    );

    // Sum[2] matches the implemented XOR with bit-1 AND.
    check_sum_bit2_logic: assert property (
        @(posedge clk) Sum[2] == (A[2] ^ B[2] ^ (A[1] & B[1]))
    );

    // Sum[3] matches the implemented XOR with bit-2 AND.
    check_sum_bit3_logic: assert property (
        @(posedge clk) Sum[3] == (A[3] ^ B[3] ^ (A[2] & B[2]))
    );

    // Cout matches the implemented carry equation.
    check_cout_logic: assert property (
        @(posedge clk) Cout == (
            ((A[0] & B[0]) & (A[1] & B[1])) |
            ((A[1] & B[1]) & (A[2] & B[2])) |
            ((A[2] & B[2]) & (A[3] & B[3])) |
            ((A[3] & B[3]) & Cin)
        )
    );

    // Upper sum bits do not depend on Cin when A and B are stable.
    check_upper_sum_independent_of_cin: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $changed(Cin)) |-> $stable(Sum[3:1])
    );

    // Sum[0] toggles with Cin when A[0] and B[0] are stable.
    check_sum0_follows_cin: assert property (
        @(posedge clk) ($stable(A[0]) && $stable(B[0]) && $changed(Cin)) |-> $changed(Sum[0])
    );

    // Cout is unchanged by Cin unless A[3] and B[3] are both high.
    check_cout_cin_gated_by_msb_and: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $changed(Cin) && !(A[3] & B[3])) |-> $stable(Cout)
    );

endmodule