module oai21x1_sva (
    input logic A,
    input logic B,
    input logic C,
    output logic Y
);
    // OAI21 logic: Y = ~(A | B) & C
    oai21_logic: assert property (
        @(posedge clk) disable iff (!reset_n) Y == ~((A | B) & C)
    );
endmodule