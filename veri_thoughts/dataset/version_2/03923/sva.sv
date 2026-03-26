module nand_7410_sva (
    input logic clk,
    input logic a1,
    input logic b1,
    input logic c1,
    input logic a2,
    input logic b2,
    input logic c2,
    input logic a3,
    input logic b3,
    input logic c3,
    input logic out1,
    input logic out2,
    input logic out3
);

    // out1 matches the 3-input NAND of a1, b1, and c1.
    check_out1_nand_function: assert property (
        @(posedge clk) out1 == ~(a1 & b1 & c1)
    );

    // out2 matches the 3-input NAND of a2, b2, and c2.
    check_out2_nand_function: assert property (
        @(posedge clk) out2 == ~(a2 & b2 & c2)
    );

    // out3 matches the 3-input NAND of a3, b3, and c3.
    check_out3_nand_function: assert property (
        @(posedge clk) out3 == ~(a3 & b3 & c3)
    );

endmodule