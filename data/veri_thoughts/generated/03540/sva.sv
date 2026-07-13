module adder_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    input logic [3:0] C
);

    // When sel is 0, C must be the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @(posedge clk) (sel === 1'b0) |-> (C === (A + B))
    );

    // When sel is not 0, C must be the bitwise AND of A and B.
    check_and_mode_result: assert property (
        @(posedge clk) (sel !== 1'b0) |-> (C === (A & B))
    );

endmodule