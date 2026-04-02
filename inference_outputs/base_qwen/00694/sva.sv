module mux2to1_sva (
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    output logic Y
);
    wire A1 = ~A1_N;
    wire A2 = ~A2_N;

    // The output Y is a combinational logic function of A1, A2, B1, and B2.
    // It is always updated on the current clock edge.
    combinational_logic: assert property (
        @(posedge clk) disable iff (!RESETn) Y == ((A1 & A2 & B2) | (A1 & ~A2 & B1) | (~A1 & A2 & B2) | (~A1 & ~A2 & B1))
    );
endmodule