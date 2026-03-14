module combinational_circuit_sva (
    input logic clk,          // external sampling clock (DUT has no clock/reset)
    input logic pullup0,
    input logic pulldown0,
    input logic HI,
    input logic LO
);
    ///// Functional equivalence to RTL assigns /////
    // HI equals pullup0 & ~pulldown0.
    check_hi_definition: assert property (
        @(posedge clk) HI == (pullup0 & ~pulldown0)
    );
    // LO equals ~pullup0 & pulldown0.
    check_lo_definition: assert property (
        @(posedge clk) LO == (~pullup0 & pulldown0)
    );

    ///// Truth-table consistency /////
    // If inputs are 1/0, then HI=1 and LO=0.
    check_truth_10_outputs: assert property (
        @(posedge clk) (pullup0 == 1'b1 && pulldown0 == 1'b0) |-> (HI == 1'b1 && LO == 1'b0)
    );
    // If inputs are 0/1, then LO=1 and HI=0.
    check_truth_01_outputs: assert property (
        @(posedge clk) (pullup0 == 1'b0 && pulldown0 == 1'b1) |-> (LO == 1'b1 && HI == 1'b0)
    );
    // If inputs are equal, both outputs are 0.
    check_equal_inputs_zero_outputs: assert property (
        @(posedge clk) (pullup0 == pulldown0) |-> (HI == 1'b0 && LO == 1'b0)
    );

    ///// Inverse implications /////
    // HI high implies inputs are 1/0.
    check_hi_implies_10: assert property (
        @(posedge clk) (HI == 1'b1) |-> (pullup0 == 1'b1 && pulldown0 == 1'b0)
    );
    // LO high implies inputs are 0/1.
    check_lo_implies_01: assert property (
        @(posedge clk) (LO == 1'b1) |-> (pullup0 == 1'b0 && pulldown0 == 1'b1)
    );
    // Both outputs low implies inputs are equal.
    check_zero_outputs_equal_inputs: assert property (
        @(posedge clk) (HI == 1'b0 && LO == 1'b0) |-> (pullup0 == pulldown0)
    );

    ///// Mutual exclusion and one-hot behavior when inputs differ /////
    // HI and LO are never both 1.
    check_outputs_mutex: assert property (
        @(posedge clk) !(HI && LO)
    );
    // When inputs differ, exactly one output is 1.
    check_one_hot_on_input_diff: assert property (
        @(posedge clk) (pullup0 != pulldown0) |-> ((HI ^ LO) == 1'b1)
    );

    ///// Simple blocking conditions /////
    // pulldown0 high blocks HI.
    check_pulldown_blocks_hi: assert property (
        @(posedge clk) (pulldown0 == 1'b1) |-> (HI == 1'b0)
    );
    // pullup0 high blocks LO.
    check_pullup_blocks_lo: assert property (
        @(posedge clk) (pullup0 == 1'b1) |-> (LO == 1'b0)
    );
endmodule