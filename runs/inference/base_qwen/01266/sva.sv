module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic Z
);
    // Combinational logic: Z is the AND of A, B, C, and D
    comb_logic: assert property (
        @(posedge clk) disable iff (!rst_n) (Z == (A & B & C & D))
    );
endmodule