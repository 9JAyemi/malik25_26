module sky130_fd_sc_hd__xor2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // X must equal A XOR B.
    check_xor_function: assert property (
        @(posedge clk) X == (A ^ B)
    );

    // When A and B are equal, X must be low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (A == B) |-> (X == 1'b0)
    );

    // When A and B differ, X must be high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (A != B) |-> (X == 1'b1)
    );

    // A high X means the inputs differ.
    check_high_output_means_inputs_differ: assert property (
        @(posedge clk) (X == 1'b1) |-> (A != B)
    );

    // A low X means the inputs are equal.
    check_low_output_means_inputs_equal: assert property (
        @(posedge clk) (X == 1'b0) |-> (A == B)
    );

endmodule