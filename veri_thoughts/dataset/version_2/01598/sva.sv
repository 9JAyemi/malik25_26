module signal_combiner_sva (
    input logic clk,           // Sampling clock for assertions (DUT is pure combinational, no reset)
    input logic input_1,
    input logic input_2,
    input logic input_3,
    input logic input_4,
    input logic output_signal
);
    // Output equals the specified sum-of-products function.
    check_functional_equivalence: assert property (
        @(posedge clk) output_signal == ((input_1 & input_2) | (input_2 & input_3) | (input_3 & input_4))
    );

    // If input_1 and input_2 are HIGH, output must be HIGH.
    check_pair12_implies_out: assert property (
        @(posedge clk) (input_1 & input_2) |-> output_signal
    );

    // If input_2 and input_3 are HIGH, output must be HIGH.
    check_pair23_implies_out: assert property (
        @(posedge clk) (input_2 & input_3) |-> output_signal
    );

    // If input_3 and input_4 are HIGH, output must be HIGH.
    check_pair34_implies_out: assert property (
        @(posedge clk) (input_3 & input_4) |-> output_signal
    );

    // If output is HIGH, at least one adjacent pair must be HIGH.
    check_out_implies_has_pair: assert property (
        @(posedge clk) output_signal |-> ((input_1 & input_2) | (input_2 & input_3) | (input_3 & input_4))
    );

    // If no adjacent pair is HIGH, output must be LOW.
    check_no_pair_implies_out0: assert property (
        @(posedge clk) ~((input_1 & input_2) | (input_2 & input_3) | (input_3 & input_4)) |-> !output_signal
    );

    // With input_2 LOW, output reduces to input_3 & input_4.
    check_i2_zero_reduction: assert property (
        @(posedge clk) (input_2 == 1'b0) |-> (output_signal == (input_3 & input_4))
    );

    // With input_3 LOW, output reduces to input_1 & input_2.
    check_i3_zero_reduction: assert property (
        @(posedge clk) (input_3 == 1'b0) |-> (output_signal == (input_1 & input_2))
    );

    // With input_2 HIGH, output reduces to input_1 | input_3.
    check_i2_one_reduction: assert property (
        @(posedge clk) (input_2 == 1'b1) |-> (output_signal == (input_1 | input_3))
    );

    // With input_3 HIGH, output reduces to input_2 | input_4.
    check_i3_one_reduction: assert property (
        @(posedge clk) (input_3 == 1'b1) |-> (output_signal == (input_2 | input_4))
    );

    // With input_1 HIGH, output reduces to input_2 | (input_3 & input_4).
    check_i1_one_reduction: assert property (
        @(posedge clk) (input_1 == 1'b1) |-> (output_signal == (input_2 | (input_3 & input_4)))
    );

    // With input_4 HIGH, output reduces to input_3 | (input_1 & input_2).
    check_i4_one_reduction: assert property (
        @(posedge clk) (input_4 == 1'b1) |-> (output_signal == (input_3 | (input_1 & input_2)))
    );

    // With input_1 LOW, output reduces to input_3 & (input_2 | input_4).
    check_i1_zero_reduction: assert property (
        @(posedge clk) (input_1 == 1'b0) |-> (output_signal == (input_3 & (input_2 | input_4)))
    );

    // With input_4 LOW, output reduces to input_2 & (input_1 | input_3).
    check_i4_zero_reduction: assert property (
        @(posedge clk) (input_4 == 1'b0) |-> (output_signal == (input_2 & (input_1 | input_3)))
    );
endmodule