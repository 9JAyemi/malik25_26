module sky130_fd_sc_hd__o2bb2ai_sva (
    input logic clk,
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y must match the implemented NAND/OR/NAND logic function.
    check_output_function: assert property (
        @(posedge clk) Y == ((A1_N & A2_N) | ((~B1) & (~B2)))
    );

    // If both B inputs are low, Y must be high.
    check_b_inputs_low_force_y_high: assert property (
        @(posedge clk) ((~B1) & (~B2)) |-> Y
    );

    // If both A inputs are high, Y must be high.
    check_a_inputs_high_force_y_high: assert property (
        @(posedge clk) (A1_N & A2_N) |-> Y
    );

    // If any B input is high and either A input is low, Y must be low.
    check_active_b_and_low_a_force_y_low: assert property (
        @(posedge clk) ((B1 | B2) & ((~A1_N) | (~A2_N))) |-> (~Y)
    );

    // A low Y must only occur when any B is high and either A is low.
    check_y_low_has_required_condition: assert property (
        @(posedge clk) (~Y) |-> ((B1 | B2) & ((~A1_N) | (~A2_N)))
    );

    // A high Y must only occur when both A are high or both B are low.
    check_y_high_has_required_condition: assert property (
        @(posedge clk) Y |-> ((A1_N & A2_N) | ((~B1) & (~B2)))
    );

endmodule