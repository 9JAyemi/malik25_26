module and2b_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B
);

    // Output implements (~A_N) & B.
    check_output_function: assert property (
        @(posedge clk) X == ((~A_N) & B)
    );

    // High A_N forces the output low.
    check_an_high_forces_x_low: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // Low B forces the output low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (X == 1'b0)
    );

    // A_N low and B high drives the output high.
    check_active_inputs_drive_x_high: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B == 1'b1)) |-> (X == 1'b1)
    );

    // High output requires A_N low and B high.
    check_x_high_implies_input_condition: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A_N == 1'b0) && (B == 1'b1))
    );

endmodule