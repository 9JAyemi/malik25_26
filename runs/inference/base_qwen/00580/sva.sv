module binary_subtractor_32bit_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] A,
    input logic [31:0] B,
    output logic [31:0] S
);
    // Combinational logic for B_comp in complement_2_32bit
    // B_comp is the 2's complement of B
    combinational_2s_comp: assert property (
        @(posedge clk) disable iff (!rst_n) (S == A + (~B + 1))
    ) else $error("B_comp calculation is incorrect");

    // Combinational logic for S in binary_subtractor_32bit
    // S is the result of A - B
    combinational_subtraction: assert property (
        @(posedge clk) disable iff (!rst_n) (S == A + (~B + 1))
    ) else $error("Subtraction result is incorrect");

endmodule