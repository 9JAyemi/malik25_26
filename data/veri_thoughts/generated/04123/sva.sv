module comparator_8bit_sva (
    input logic       clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic       match
);

    // Combinational DUT with no reset; assertions are sampled on an external clock.

    // match must equal the AND of all per-bit equality results.
    check_match_bitwise_implementation: assert property (
        @(posedge clk)
        match == (
            (in1[0] == in2[0]) &
            (in1[1] == in2[1]) &
            (in1[2] == in2[2]) &
            (in1[3] == in2[3]) &
            (in1[4] == in2[4]) &
            (in1[5] == in2[5]) &
            (in1[6] == in2[6]) &
            (in1[7] == in2[7])
        )
    );

    // Equal input vectors must produce a match.
    check_equal_inputs_set_match: assert property (
        @(posedge clk)
        (in1 == in2) |-> (match == 1'b1)
    );

    // Unequal input vectors must clear match.
    check_unequal_inputs_clear_match: assert property (
        @(posedge clk)
        (in1 != in2) |-> (match == 1'b0)
    );

    // A high match output means the two inputs are equal.
    check_match_high_means_equal: assert property (
        @(posedge clk)
        (match == 1'b1) |-> (in1 == in2)
    );

    // A low match output means the two inputs are not equal.
    check_match_low_means_unequal: assert property (
        @(posedge clk)
        (match == 1'b0) |-> (in1 != in2)
    );

endmodule