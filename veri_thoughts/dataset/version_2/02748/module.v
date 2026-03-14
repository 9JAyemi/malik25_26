module dual_edge_ff (
    input clk,
    input d,
    output q
);

    wire d1;
    wire q1;

    // First stage D flip-flop
    DFF dff1 (.clk(clk), .d(d), .q(d1));

    // Second stage D flip-flop
    DFF dff2 (.clk(clk), .d(d1), .q(q1));

    // Third stage D flip-flop
    DFF dff3 (.clk(clk), .d(q1), .q(q));

endmodule

module DFF (
    input clk,
    input d,
    output q
);

    reg q;

    always @(posedge clk)
        q <= d;

endmodule