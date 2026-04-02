module and_gate_extra_sva (
    input logic A,
    input logic B,
    input logic C,
    output logic Y
);
    // Combinational logic: Y is the result of A & B & ~C
    // This assertion checks that Y is correctly calculated based on the inputs A, B, and C
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == (A & B & ~C))
    );
endmodule