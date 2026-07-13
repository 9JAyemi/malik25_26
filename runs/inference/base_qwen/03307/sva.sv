module adder_sva(
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] S,
    input logic C_out
);
    // Combinational logic: S should be the lower 8 bits of A + B
    comb_sum: assert property (
        @(posedge clk) $rose(C_out) |-> (S == (A + B)[7:0])
    );
    // Combinational logic: C_out should be the carry bit of A + B
    comb_carry: assert property (
        @(posedge clk) $rose(C_out) |-> (C_out == (A + B)[8])
    );
endmodule