module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    output logic [7:0] C
);
    // Combinational logic: C is the bitwise AND of A and B
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (C == (A & B))
    );
endmodule