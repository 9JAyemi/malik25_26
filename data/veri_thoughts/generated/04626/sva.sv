module IP6S_sva (
    input logic CK,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic n1,
    input logic n2,
    input logic n3,
    input logic n4,
    input logic n5,
    input logic n6,
    input logic n7,
    input logic n8,
    input logic n9
);

    // n1 is the NAND of in3 and in4.
    check_n1_nand_function: assert property (
        @(posedge CK) n1 === ~(in3 & in4)
    );

    // n2 captures n1 on the next rising edge.
    check_n2_dff_behavior: assert property (
        @(posedge CK) 1'b1 |=> (n2 === $past(n1))
    );

    // n3 is the inversion of n2.
    check_n3_inverts_n2: assert property (
        @(posedge CK) n3 === ~n2
    );

    // n6 is the NAND of in2 and n2.
    check_n6_nand_function: assert property (
        @(posedge CK) n6 === ~(in2 & n2)
    );

    // n4 is the NAND of in5 and n3.
    check_n4_nand_function: assert property (
        @(posedge CK) n4 === ~(in5 & n3)
    );

    // n5 captures n4 on the next rising edge.
    check_n5_dff_behavior: assert property (
        @(posedge CK) 1'b1 |=> (n5 === $past(n4))
    );

    // n7 is the AND of in1, n6, and n5.
    check_n7_and_function: assert property (
        @(posedge CK) n7 === (in1 & n6 & n5)
    );

    // n8 is the inversion of n5.
    check_n8_inverts_n5: assert property (
        @(posedge CK) n8 === ~n5
    );

    // n9 captures n8 on the next rising edge.
    check_n9_dff_behavior: assert property (
        @(posedge CK) 1'b1 |=> (n9 === $past(n8))
    );

    // out1 captures n6 on the next rising edge.
    check_out1_dff_behavior: assert property (
        @(posedge CK) 1'b1 |=> (out1 === $past(n6))
    );

    // out2 is the NOR of n7 and n9.
    check_out2_nor_function: assert property (
        @(posedge CK) out2 === ~(n7 | n9)
    );

    // out3 is the NOR of n9 and in6.
    check_out3_nor_function: assert property (
        @(posedge CK) out3 === ~(n9 | in6)
    );

endmodule