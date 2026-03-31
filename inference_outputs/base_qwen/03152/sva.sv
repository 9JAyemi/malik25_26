```systemverilog
module nand2_en_sva (
    input logic A,
    input logic B,
    input logic EN,
    output logic Z
);
    // NAND1 gate output should be the negation of the AND of A and B
    nand1_output: assert property (
        @(posedge clk) disable iff (!rst_n) Z == ~(A & B)
    );

    // NAND2 gate output should be the negation of the AND of NAND1 output and EN
    nand2_output: assert property (
        @(posedge clk) disable iff (!rst_n) Z == ~((~(A & B)) & EN)
    );

    // AND gate output should be the AND of A and B
    and_output: assert property (
        @(posedge clk) disable iff (!rst_n) Z == ((A & B) & ~((A & B)) & EN)
    );
endmodule
```