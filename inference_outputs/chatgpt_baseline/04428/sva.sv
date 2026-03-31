module comparator_assertions (
    input logic        clk,
    input logic [3:0]  in0,
    input logic [3:0]  in1,
    input logic [1:0]  result,
    input logic [3:0]  in0_reg,
    input logic [3:0]  in1_reg
);

    // in0_reg mirrors in0 after the first input-driven update.
    check_in0_reg_tracks_in0: assert property (
        @(posedge clk) !$initstate |-> (in0_reg == in0)
    );

    // in1_reg mirrors in1 after the first input-driven update.
    check_in1_reg_tracks_in1: assert property (
        @(posedge clk) !$initstate |-> (in1_reg == in1)
    );

    // result only uses the implemented output encodings.
    check_result_encoding: assert property (
        @(posedge clk) !$initstate |-> ((result == 2'b00) || (result == 2'b01) || (result == 2'b10))
    );

    // A previous greater-than comparison drives result to 01.
    check_prev_gt_sets_result_gt: assert property (
        @(posedge clk) (!$initstate && ($past(in0_reg) > $past(in1_reg))) |-> (result == 2'b01)
    );

    // A previous less-than comparison drives result to 10.
    check_prev_lt_sets_result_lt: assert property (
        @(posedge clk) (!$initstate && ($past(in0_reg) < $past(in1_reg))) |-> (result == 2'b10)
    );

    // A previous equality comparison drives result to 00.
    check_prev_eq_sets_result_eq: assert property (
        @(posedge clk) (!$initstate && ($past(in0_reg) == $past(in1_reg))) |-> (result == 2'b00)
    );

    // result 01 only comes from a previous greater-than comparison.
    check_result_gt_implies_prev_gt: assert property (
        @(posedge clk) (!$initstate && (result == 2'b01)) |-> ($past(in0_reg) > $past(in1_reg))
    );

    // result 10 only comes from a previous less-than comparison.
    check_result_lt_implies_prev_lt: assert property (
        @(posedge clk) (!$initstate && (result == 2'b10)) |-> ($past(in0_reg) < $past(in1_reg))
    );

    // result 00 only comes from a previous equality comparison.
    check_result_eq_implies_prev_eq: assert property (
        @(posedge clk) (!$initstate && (result == 2'b00)) |-> ($past(in0_reg) == $past(in1_reg))
    );

endmodule