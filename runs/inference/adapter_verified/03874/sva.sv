module NAND4AND2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] Z
);

// Z[1] is the NAND of the two 2-input NANDs.
    check_z1_function: assert property (
        @(posedge clk) Z[1] == ~( ~(A & B) & ~(C & D) )
    );

// Z[0] is the NAND of Z[1] with itself.
    check_z0_function: assert property (
        @(posedge clk) Z[0] == ~(Z[1] & Z[1])
    );

// Z[1] is always high because the two 2-input NANDs are never both low.
    check_z1_always_high: assert property (
        @(posedge clk) Z[1] == 1'b1
    );

// Z[0] is always low because Z[1] is always high.
    check_z0_always_low: assert property (
        @(posedge clk) Z[0] == 1'b0
    );

// The full 2-bit output is always 10.
    check_full_output: assert property (
        @(posedge clk) Z == 2'b10
    );

endmodule
