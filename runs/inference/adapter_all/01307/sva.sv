module top_module_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0]  SEL,
    input logic [15:0] result
);

    // When SEL[1] is low, result comes from the adder path.
    check_result_selects_adder: assert property (
        @(posedge clk) !SEL[1] |-> (result == (A + B))
    );

    // When SEL[1] is high, result comes from the barrel shifter path.
    check_result_selects_shifter: assert property (
        @(posedge clk) SEL[1] |-> (result == (SEL[0] ? (A >> B) : (A << B)))
    );

    // With SEL[1] low and SEL[0] low, result is A plus B.
    check_add_mode: assert property (
        @(posedge clk) (!SEL[1] && !SEL[0]) |-> (result == (A + B))
    );

    // With SEL[1] low and SEL[0] high, result is A minus B.
    check_sub_mode: assert property (
        @(posedge clk) (!SEL[1] && SEL[0]) |-> (result == (A - B))
    );

    // With SEL[1] high and SEL[0] low, result is A left-shifted by B.
    check_left_shift_mode: assert property (
        @(posedge clk) (SEL[1] && !SEL[0]) |-> (result == (A << B))
    );

    // With SEL[1] high and SEL[0] high, result is A right-shifted by B.
    check_right_shift_mode: assert property (
        @(posedge clk) (SEL[1] && SEL[0]) |-> (result == (A >> B))
    );

    // With SEL[1] low and B equal to zero, addition passes A through.
    check_add_zero_b_passthrough: assert property (
        @(posedge clk) (!SEL[1] && (B == 16'h0000)) |-> (result == A)
    );

    // With SEL[1] low and B equal to zero, subtraction passes A through.
    check_sub_zero_b_passthrough: assert property (
        @(posedge clk) (!SEL[1] && SEL[0] && (B == 16'h0000)) |-> (result == A)
    );

    // With SEL[1] high and B equal to zero, left shift passes A through.
    check_left_shift_zero_b_passthrough: assert property (
        @(posedge clk) (SEL[1] && !SEL[0] && (B == 16'h0000)) |-> (result == A)
    );

    // With SEL[1] high and B equal to zero, right shift passes A through.
    check_right_shift_zero_b_passthrough: assert property (
        @(posedge clk) (SEL[1] && SEL[0] && (B == 16'h0000)) |-> (result == A)
    );

endmodule