module adder_subtractor_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       ctrl,
    input logic [3:0] Z
);

    // In add mode, Z is the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @(posedge clk) (ctrl == 1'b0) |-> (Z == (A + B))
    );

    // In subtract mode, Z is the 4-bit difference of A and B.
    check_subtract_mode_result: assert property (
        @(posedge clk) (ctrl == 1'b1) |-> (Z == (A - B))
    );

    // Subtracting equal operands produces zero.
    check_equal_operands_subtract_to_zero: assert property (
        @(posedge clk) (ctrl == 1'b1 && A == B) |-> (Z == 4'b0000)
    );

endmodule