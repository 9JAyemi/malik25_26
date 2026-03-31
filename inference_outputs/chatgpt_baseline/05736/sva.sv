module xnor2_assertions (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y matches the RTL XNOR function of A and B.
    check_y_matches_xnor_function: assert property (
        @(posedge clk) (Y == ~(A ^ B))
    );

    // A=0 and B=0 drive Y high.
    check_00_outputs_high: assert property (
        @(posedge clk) ((!A && !B) |-> (Y == 1'b1))
    );

    // A=0 and B=1 drive Y low.
    check_01_outputs_low: assert property (
        @(posedge clk) ((!A && B) |-> (Y == 1'b0))
    );

    // A=1 and B=0 drive Y low.
    check_10_outputs_low: assert property (
        @(posedge clk) ((A && !B) |-> (Y == 1'b0))
    );

    // A=1 and B=1 drive Y high.
    check_11_outputs_high: assert property (
        @(posedge clk) ((A && B) |-> (Y == 1'b1))
    );

endmodule