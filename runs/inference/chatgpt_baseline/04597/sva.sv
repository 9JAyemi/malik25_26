module mux_2_1_sva (
    input logic clk,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

    // Out matches the implemented mux equation.
    check_mux_boolean_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        out == ((in0 & ~sel) | (in1 & sel))
    );

    // When sel is low, out follows in0.
    check_sel_low_routes_in0: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 1'b0) |-> (out == in0)
    );

    // When sel is high, out follows in1.
    check_sel_high_routes_in1: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 1'b1) |-> (out == in1)
    );

    // If both inputs are low, out is low.
    check_both_inputs_low_drive_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (in0 == 1'b0 && in1 == 1'b0) |-> (out == 1'b0)
    );

    // If both inputs are high, out is high.
    check_both_inputs_high_drive_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (in0 == 1'b1 && in1 == 1'b1) |-> (out == 1'b1)
    );

    // With in0 high and in1 low, out is the inverse of sel.
    check_in0_high_in1_low_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (in0 == 1'b1 && in1 == 1'b0) |-> (out == ~sel)
    );

    // With in0 low and in1 high, out matches sel.
    check_in0_low_in1_high_case: assert property (
        @(posedge clk) disable iff (1'b0)
        (in0 == 1'b0 && in1 == 1'b1) |-> (out == sel)
    );

endmodule