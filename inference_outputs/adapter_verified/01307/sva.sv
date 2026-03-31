module top_module_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] SEL,
    input logic [15:0] result
);

// When SEL[1] is 0, result must come from the adder_subtractor.
    check_result_from_add_sub_when_sel1_low: assert property (
        @(posedge clk) !SEL[1] |-> (result == add_sub_out)
    );

// When SEL[1] is 1, result must come from the barrel_shifter.
    check_result_from_shift_when_sel1_high: assert property (
        @(posedge clk) SEL[1] |-> (result == shift_out)
    );

// With SEL[1] low and SEL[0] low, result must be A + B.
    check_add_result_when_sel100: assert property (
        @(posedge clk) (!SEL[1] && !SEL[0]) |-> (result == (A + B))
    );

// With SEL[1] low and SEL[0] high, result must be A - B.
    check_sub_result_when_sel101: assert property (
        @(posedge clk) (!SEL[1] && SEL[0]) |-> (result == (A - B))
    );

// With SEL[1] high and SEL[0] low, result must be A << B.
    check_shift_left_result_when_sel110: assert property (
        @(posedge clk) (SEL[1] && !SEL[0]) |-> (result == (A << B))
    );

// With SEL[1] high and SEL[0] high, result must be A >> B.
    check_shift_right_result_when_sel111: assert property (
        @(posedge clk) (SEL[1] && SEL[0]) |-> (result == (A >> B))
    );

endmodule
