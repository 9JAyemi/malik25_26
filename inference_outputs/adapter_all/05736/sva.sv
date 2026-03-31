module xnor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

    // Y must always equal the XNOR of A and B.
    check_xnor_function: assert property (
        @(posedge clk) Y == ~(A ^ B)
    );

    // When both inputs are low, Y must be high.
    check_xnor_00: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // When both inputs are high, Y must be high.
    check_xnor_11: assert property (
        @(posedge clk) (A && B) |-> Y
    );

    // When the inputs differ, Y must be low.
    check_xnor_mismatch: assert property (
        @(posedge clk) (A ^ B) |-> !Y
    );

    // A high Y means the inputs must match.
    check_xnor_high_matches: assert property (
        @(posedge clk) Y |-> !(A ^ B)
    );

    // A low Y means the inputs must differ.
    check_xnor_low_mismatch: assert property (
        @(posedge clk) !Y |-> (A ^ B)
    );

endmodule