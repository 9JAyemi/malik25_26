module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // Combinational logic, so use @(posedge clk)
    // Check that the output C is the bitwise AND of A and B
    check_and_result: assert property (
        @(posedge clk) $rose(C) |-> (C == (A & B))
    );

endmodule