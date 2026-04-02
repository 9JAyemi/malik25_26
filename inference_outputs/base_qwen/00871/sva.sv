module and_gate_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic reset,
    output logic X
);
    // At reset, output X should be LOW.
    reset: assert property (
        @(posedge clk) disable iff (!reset) X == 1'b0
    );

    // Sequential logic: X should be the AND of A and B.
    sequential_logic: assert property (
        @(posedge clk) disable iff (!reset) X == (A & B)
    );
endmodule