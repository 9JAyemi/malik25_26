module fsm_priority_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out1,
    input logic out2
);

    // in1 has highest priority and selects the S0 output pattern.
    check_in1_priority_output: assert property (
        @(posedge clk) in1 |-> (out1 == 1'b1 && out2 == 1'b0)
    );

    // in2 selects the S1 output pattern when in1 is low.
    check_in2_priority_output: assert property (
        @(posedge clk) (!in1 && in2) |-> (out1 == 1'b0 && out2 == 1'b1)
    );

    // in3 selects the S2 output pattern when higher-priority inputs are low.
    check_in3_priority_output: assert property (
        @(posedge clk) (!in1 && !in2 && in3) |-> (out1 == 1'b1 && out2 == 1'b1)
    );

    // No asserted inputs selects the S3 output pattern.
    check_no_input_output: assert property (
        @(posedge clk) (!in1 && !in2 && !in3) |-> (out1 == 1'b0 && out2 == 1'b0)
    );

    // Output 10 only occurs when in1 is asserted.
    check_output_10_source: assert property (
        @(posedge clk) (out1 == 1'b1 && out2 == 1'b0) |-> in1
    );

    // Output 01 only occurs when in1 is low and in2 is asserted.
    check_output_01_source: assert property (
        @(posedge clk) (out1 == 1'b0 && out2 == 1'b1) |-> (!in1 && in2)
    );

    // Output 11 only occurs when only in3 wins the priority selection.
    check_output_11_source: assert property (
        @(posedge clk) (out1 == 1'b1 && out2 == 1'b1) |-> (!in1 && !in2 && in3)
    );

    // Output 00 only occurs when all inputs are deasserted.
    check_output_00_source: assert property (
        @(posedge clk) (out1 == 1'b0 && out2 == 1'b0) |-> (!in1 && !in2 && !in3)
    );

endmodule