module AND4_sva (
    input logic clk,
    input logic out1,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4
);

    // Output must equal the 4-input AND of all inputs.
    check_out1_matches_and4: assert property (
        @(posedge clk) (out1 == (in1 & in2 & in3 & in4))
    );

    // When all inputs are high, the output must be high.
    check_all_high_drives_out1_high: assert property (
        @(posedge clk)
        (((in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1)) |-> (out1 == 1'b1))
    );

    // A high output implies all four inputs are high.
    check_out1_high_implies_all_high: assert property (
        @(posedge clk)
        ((out1 == 1'b1) |-> ((in1 == 1'b1) && (in2 == 1'b1) && (in3 == 1'b1) && (in4 == 1'b1)))
    );

    // A low in1 must force the output low.
    check_in1_low_forces_out1_low: assert property (
        @(posedge clk) ((in1 == 1'b0) |-> (out1 == 1'b0))
    );

    // A low in2 must force the output low.
    check_in2_low_forces_out1_low: assert property (
        @(posedge clk) ((in2 == 1'b0) |-> (out1 == 1'b0))
    );

    // A low in3 must force the output low.
    check_in3_low_forces_out1_low: assert property (
        @(posedge clk) ((in3 == 1'b0) |-> (out1 == 1'b0))
    );

    // A low in4 must force the output low.
    check_in4_low_forces_out1_low: assert property (
        @(posedge clk) ((in4 == 1'b0) |-> (out1 == 1'b0))
    );

endmodule