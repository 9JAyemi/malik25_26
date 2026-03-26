module adder_tree_top_sva (
    input logic       clk,
    input logic [6:0] isum0_0_0_0,
    input logic [6:0] isum0_0_0_1,
    input logic [6:0] isum0_0_1_0,
    input logic [6:0] isum0_0_1_1,
    input logic [6:0] isum0_1_0_0,
    input logic [6:0] isum0_1_0_1,
    input logic [6:0] isum0_1_1_0,
    input logic [6:0] isum0_1_1_1,
    input logic [7:0] sum
);

    // Clock: clk; no reset in RTL.
    // Registered inputs feed combinational adders.
    // `2_LEVEL_ADDER makes sum use only the first four sampled inputs.

    function automatic [7:0] expected_sum4 (
        input logic [6:0] a,
        input logic [6:0] b,
        input logic [6:0] c,
        input logic [6:0] d
    );
        expected_sum4 = {1'b0, a} + {1'b0, b} + {1'b0, c} + {1'b0, d};
    endfunction

    // Sum matches the registered first four inputs one cycle later.
    check_sum_matches_registered_first_four: assert property (
        @(posedge clk) disable iff ($initstate)
        1'b1 |=> sum == expected_sum4(
            $past(isum0_0_0_0),
            $past(isum0_0_0_1),
            $past(isum0_0_1_0),
            $past(isum0_0_1_1)
        )
    );

    // All used inputs low produce a zero sum on the next cycle.
    check_zero_when_used_inputs_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'd0 &&
         isum0_0_0_1 == 7'd0 &&
         isum0_0_1_0 == 7'd0 &&
         isum0_0_1_1 == 7'd0) |=> (sum == 8'd0)
    );

    // The second group of four inputs does not affect sum in 2-level mode.
    check_upper_branch_unused: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'd0 &&
         isum0_0_0_1 == 7'd0 &&
         isum0_0_1_0 == 7'd0 &&
         isum0_0_1_1 == 7'd0 &&
         (isum0_1_0_0 != 7'd0 ||
          isum0_1_0_1 != 7'd0 ||
          isum0_1_1_0 != 7'd0 ||
          isum0_1_1_1 != 7'd0)) |=> (sum == 8'd0)
    );

    // With only the first used input active, sum passes that value through.
    check_input0_passthrough: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_1 == 7'd0 &&
         isum0_0_1_0 == 7'd0 &&
         isum0_0_1_1 == 7'd0) |=> (sum == {1'b0, $past(isum0_0_0_0)})
    );

    // With only the second used input active, sum passes that value through.
    check_input1_passthrough: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'd0 &&
         isum0_0_1_0 == 7'd0 &&
         isum0_0_1_1 == 7'd0) |=> (sum == {1'b0, $past(isum0_0_0_1)})
    );

    // With only the third used input active, sum passes that value through.
    check_input2_passthrough: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'd0 &&
         isum0_0_0_1 == 7'd0 &&
         isum0_0_1_1 == 7'd0) |=> (sum == {1'b0, $past(isum0_0_1_0)})
    );

    // With only the fourth used input active, sum passes that value through.
    check_input3_passthrough: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'd0 &&
         isum0_0_0_1 == 7'd0 &&
         isum0_0_1_0 == 7'd0) |=> (sum == {1'b0, $past(isum0_0_1_1)})
    );

    // Full-scale used inputs overflow and truncate to the low 8 bits.
    check_full_scale_truncation: assert property (
        @(posedge clk) disable iff ($initstate)
        (isum0_0_0_0 == 7'h7f &&
         isum0_0_0_1 == 7'h7f &&
         isum0_0_1_0 == 7'h7f &&
         isum0_0_1_1 == 7'h7f) |=> (sum == 8'hfc)
    );

endmodule