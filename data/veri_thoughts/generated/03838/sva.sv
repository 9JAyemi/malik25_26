module SaturationEnhancement_sva (
    input logic clk,
    input logic signed [15:0] in1,
    input logic signed [15:0] in2,
    input logic signed [15:0] T,
    input logic signed [15:0] out1,
    input logic signed [15:0] out2
);

    // out1 must match the RTL expression driven from in1 and T.
    check_out1_matches_rtl: assert property (
        @(posedge clk)
        out1 == (($signed(((in1 < 0) ? -in1 : in1)) <= T) ? in1 : $signed(((in1 < 0) ? -T : T)))
    );

    // out2 must match the RTL expression driven from in2 and T.
    check_out2_matches_rtl: assert property (
        @(posedge clk)
        out2 == (($signed(((in2 < 0) ? -in2 : in2)) <= T) ? in2 : $signed(((in2 < 0) ? -T : T)))
    );

    // If in1 is within the signed threshold comparison, out1 passes through.
    check_out1_passthrough: assert property (
        @(posedge clk)
        ($signed(((in1 < 0) ? -in1 : in1)) <= T) |-> (out1 == in1)
    );

    // If in2 is within the signed threshold comparison, out2 passes through.
    check_out2_passthrough: assert property (
        @(posedge clk)
        ($signed(((in2 < 0) ? -in2 : in2)) <= T) |-> (out2 == in2)
    );

    // If in1 exceeds the signed threshold comparison, out1 selects T or -T.
    check_out1_clamps_to_threshold_value: assert property (
        @(posedge clk)
        ($signed(((in1 < 0) ? -in1 : in1)) > T) |-> (out1 == $signed(((in1 < 0) ? -T : T)))
    );

    // If in2 exceeds the signed threshold comparison, out2 selects T or -T.
    check_out2_clamps_to_threshold_value: assert property (
        @(posedge clk)
        ($signed(((in2 < 0) ? -in2 : in2)) > T) |-> (out2 == $signed(((in2 < 0) ? -T : T)))
    );

    // Equal channel inputs must produce equal channel outputs.
    check_equal_inputs_produce_equal_outputs: assert property (
        @(posedge clk)
        (in1 == in2) |-> (out1 == out2)
    );

endmodule