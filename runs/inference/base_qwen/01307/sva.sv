module top_module_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] SEL,
    output logic [15:0] result
);

    // Assertions for the top_module

    // The result should be either the output of the adder_subtractor or the barrel_shifter based on SEL[1]
    result_assignment: assert property (
        @(posedge clk) disable iff (!clk) (result == (SEL[1]) ? shift_out : add_sub_out)
    );

    // Assertions for the adder_subtractor

    // The output of the adder_subtractor should be the sum of A and B when SEL[0] is 0
    adder_sum: assert property (
        @(posedge clk) disable iff (!clk) (SEL[0] == 1'b0) |-> (add_sub_out == (A + B))
    );

    // The output of the adder_subtractor should be the difference of A and B when SEL[0] is 1
    adder_difference: assert property (
        @(posedge clk) disable iff (!clk) (SEL[0] == 1'b1) |-> (add_sub_out == (A - B))
    );

    // Assertions for the barrel_shifter

    // The output of the barrel_shifter should be the left shift of A by B when SEL[0] is 0
    left_shift: assert property (
        @(posedge clk) disable iff (!clk) (SEL[0] == 1'b0) |-> (shift_out == (A << B))
    );

    // The output of the barrel_shifter should be the right shift of A by B when SEL[0] is 1
    right_shift: assert property (
        @(posedge clk) disable iff (!clk) (SEL[0] == 1'b1) |-> (shift_out == (A >> B))
    );

endmodule