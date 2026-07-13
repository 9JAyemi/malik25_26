module xnor2_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B
);

// Y must equal the XNOR of A and B.
    check_xnor_function: assert property (
        @(posedge clk) Y == ~(A ^ B)
    );

// When A and B are equal, Y must be HIGH.
    check_equal_inputs_drive_high: assert property (
        @(posedge clk) (A == B) |-> (Y == 1'b1)
    );

// When A and B differ, Y must be LOW.
    check_different_inputs_drive_low: assert property (
        @(posedge clk) (A != B) |-> (Y == 1'b0)
    );

endmodule
