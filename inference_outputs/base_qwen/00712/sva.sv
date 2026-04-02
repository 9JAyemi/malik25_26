module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C
);
    // Combinational logic: C should always be the sum of A and B
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) C == A + B
    );
endmodule