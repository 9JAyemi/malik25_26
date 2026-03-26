module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // sel1=0 and sel0=0 must route in0 to out.
    check_select_00_routes_in0: assert property (
        @(posedge clk) ((sel1 == 1'b0) && (sel0 == 1'b0)) |-> (out == in0)
    );

    // sel1=0 and sel0=1 must route in1 to out.
    check_select_01_routes_in1: assert property (
        @(posedge clk) ((sel1 == 1'b0) && (sel0 == 1'b1)) |-> (out == in1)
    );

    // sel1=1 and sel0=0 must route in2 to out.
    check_select_10_routes_in2: assert property (
        @(posedge clk) ((sel1 == 1'b1) && (sel0 == 1'b0)) |-> (out == in2)
    );

    // sel1=1 and sel0=1 must route in3 to out.
    check_select_11_routes_in3: assert property (
        @(posedge clk) ((sel1 == 1'b1) && (sel0 == 1'b1)) |-> (out == in3)
    );

    // When the lower pair matches and sel1 selects it, sel0 cannot change out.
    check_sel1_low_equal_lower_pair: assert property (
        @(posedge clk) ((sel1 == 1'b0) && (in0 == in1)) |-> (out == in0)
    );

    // When the upper pair matches and sel1 selects it, sel0 cannot change out.
    check_sel1_high_equal_upper_pair: assert property (
        @(posedge clk) ((sel1 == 1'b1) && (in2 == in3)) |-> (out == in2)
    );

    // When left-side inputs match and sel0 selects them, sel1 cannot change out.
    check_sel0_low_equal_left_inputs: assert property (
        @(posedge clk) ((sel0 == 1'b0) && (in0 == in2)) |-> (out == in0)
    );

    // When right-side inputs match and sel0 selects them, sel1 cannot change out.
    check_sel0_high_equal_right_inputs: assert property (
        @(posedge clk) ((sel0 == 1'b1) && (in1 == in3)) |-> (out == in1)
    );

endmodule