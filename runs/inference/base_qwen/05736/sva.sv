module xnor2_sva (
    input logic Y,
    input logic A,
    input logic B
);
    // The logic is purely combinational, so we will use @(posedge clk) for assertions.
    // The output Y is the XNOR of inputs A and B.

    // Y should always be the XNOR of A and B.
    xnor_property: assert property (
        @(posedge clk) disable iff (!reset_n) (Y == ~(A ^ B))
    );
endmodule