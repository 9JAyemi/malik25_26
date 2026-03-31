module top_module_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] SEL,
    input logic [15:0] result
);

    // When SEL[1] is low, result comes from the adder path.
    check_select_add_path: assert property (
        @(posedge clk) !SEL[1] |-> (result == ((SEL[0]) ? (A - B) : (A + B)))
    );

    // When SEL[1] is high, result comes from the barrel shifter path.
    check_select_shift_path: assert property (
        @(posedge clk) SEL[1] |-> (result == ((SEL[0]) ? (A >> B) : (A << B)))
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

endmodule