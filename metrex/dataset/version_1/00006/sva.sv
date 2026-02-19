module v144728_sva (
    // Clock for sampling combinational assertions
    input  logic clk,

    // DUT ports
    input  logic v6dda25,
    input  logic v27dec4,
    input  logic v92a149,
    input  logic v4642b6
);

    ////////////////////////////////////////////////////////////////////////////////
    // v144728 is purely combinational and implements:
    //   v4642b6 = v6dda25 & v27dec4 & v92a149
    // No reset is present in the RTL. All properties are sampled on posedge clk.
    ////////////////////////////////////////////////////////////////////////////////

    // Functional equivalence: Output equals the 3-input AND of the inputs.
    check_and3_equivalence: assert property (
        @(posedge clk) v4642b6 == (v6dda25 & v27dec4 & v92a149)
    );

    // Dominance of zeros: If v6dda25 is 0, the output must be 0.
    check_zero_if_v6dda25_zero: assert property (
        @(posedge clk) (v6dda25 == 1'b0) |-> (v4642b6 == 1'b0)
    );

    // Dominance of zeros: If v27dec4 is 0, the output must be 0.
    check_zero_if_v27dec4_zero: assert property (
        @(posedge clk) (v27dec4 == 1'b0) |-> (v4642b6 == 1'b0)
    );

    // Dominance of zeros: If v92a149 is 0, the output must be 0.
    check_zero_if_v92a149_zero: assert property (
        @(posedge clk) (v92a149 == 1'b0) |-> (v4642b6 == 1'b0)
    );

    // High implies all inputs high: If output is 1, all three inputs must be 1.
    check_output_implies_inputs_high: assert property (
        @(posedge clk) (v4642b6 == 1'b1) |-> (v6dda25 == 1'b1) && (v27dec4 == 1'b1) && (v92a149 == 1'b1)
    );

    // All inputs high implies output high.
    check_all_inputs_high_implies_output_high: assert property (
        @(posedge clk) (v6dda25 == 1'b1) && (v27dec4 == 1'b1) && (v92a149 == 1'b1) |-> (v4642b6 == 1'b1)
    );

    // When v92a149 and v27dec4 are high, output tracks v6dda25.
    check_tracks_v6dda25_when_other_two_high: assert property (
        @(posedge clk) (v92a149 == 1'b1) && (v27dec4 == 1'b1) |-> (v4642b6 == v6dda25)
    );

    // When v6dda25 and v92a149 are high, output tracks v27dec4.
    check_tracks_v27dec4_when_other_two_high: assert property (
        @(posedge clk) (v6dda25 == 1'b1) && (v92a149 == 1'b1) |-> (v4642b6 == v27dec4)
    );

    // When v6dda25 and v27dec4 are high, output tracks v92a149.
    check_tracks_v92a149_when_other_two_high: assert property (
        @(posedge clk) (v6dda25 == 1'b1) && (v27dec4 == 1'b1) |-> (v4642b6 == v92a149)
    );

    // Conditional reduction via mux structure: If v92a149==1 and v27dec4==0, output must be 0.
    check_mux_path_v92a149_1_v27dec4_0: assert property (
        @(posedge clk) (v92a149 == 1'b1) && (v27dec4 == 1'b0) |-> (v4642b6 == 1'b0)
    );

endmodule