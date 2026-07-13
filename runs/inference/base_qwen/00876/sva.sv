module three_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    output logic Y
);
    // Output logic behavior
    // Y is the result of (A1 & A2) | B1
    output_behavior: assert property (
        @(posedge clk) disable iff (!RESETn) Y == ((A1 & A2) | B1)
    );
endmodule