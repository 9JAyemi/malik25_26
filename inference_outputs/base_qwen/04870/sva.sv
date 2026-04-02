module logical_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    // Y is the result of A AND B AND C
    logic_and_result: assert property (
        @(posedge clk) disable iff (!rst_n) Y == (A & B & C)
    );
endmodule