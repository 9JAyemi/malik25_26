module three_bit_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co,
    input logic n1,
    input logic n2,
    input logic n3,
    input logic n4,
    input logic n5,
    input logic n6,
    input logic n7,
    input logic n8,
    input logic n9,
    input logic n10,
    input logic n11
);

    // n1 is the XOR of A and B.
    check_n1_xor_ab: assert property (
        @(posedge clk) n1 == (A ^ B)
    );

    // S is the XOR of n1 and Ci.
    check_sum_from_n1_and_ci: assert property (
        @(posedge clk) S == (n1 ^ Ci)
    );

    // n2 is the AND of A and B.
    check_n2_and_ab: assert property (
        @(posedge clk) n2 == (A & B)
    );

    // n3 is the AND of n1 and Ci.
    check_n3_and_n1_ci: assert property (
        @(posedge clk) n3 == (n1 & Ci)
    );

    // Co is the OR of n2 and n3.
    check_carry_from_n2_or_n3: assert property (
        @(posedge clk) Co == (n2 | n3)
    );

    // The outputs match 1-bit addition of A, B, and Ci.
    check_full_adder_numeric_result: assert property (
        @(posedge clk) {Co, S} == ({1'b0, A} + {1'b0, B} + {1'b0, Ci})
    );

    // n4 is the AND of n2 and n3.
    check_n4_and_n2_n3: assert property (
        @(posedge clk) n4 == (n2 & n3)
    );

    // n5 is the OR of n4 and n3.
    check_n5_or_n4_n3: assert property (
        @(posedge clk) n5 == (n4 | n3)
    );

    // n6 is the inversion of n5.
    check_n6_inverts_n5: assert property (
        @(posedge clk) n6 == (~n5)
    );

    // n7 duplicates the AND of n2 and n3.
    check_n7_and_n2_n3: assert property (
        @(posedge clk) n7 == (n2 & n3)
    );

    // n8 duplicates the AND of n1 and Ci.
    check_n8_and_n1_ci: assert property (
        @(posedge clk) n8 == (n1 & Ci)
    );

    // n9 is the OR of n7 and n8.
    check_n9_or_n7_n8: assert property (
        @(posedge clk) n9 == (n7 | n8)
    );

    // n10 is the inversion of n9.
    check_n10_inverts_n9: assert property (
        @(posedge clk) n10 == (~n9)
    );

    // n11 duplicates the AND of n2 and n3.
    check_n11_and_n2_n3: assert property (
        @(posedge clk) n11 == (n2 & n3)
    );

endmodule