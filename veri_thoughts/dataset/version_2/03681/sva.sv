module adder_subtractor_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        C,
    input logic        CLK,
    input logic [15:0] R
);

    // R must hold the prior cycle's selected add/sub result.
    check_registered_result: assert property (
        @(posedge CLK) disable iff ($initstate)
        R == (($past(C) == 1'b1) ? ($past(A) - $past(B)) : ($past(A) + $past(B)))
    );

    // In add mode, R captures the prior cycle sum.
    check_addition_mode_result: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(C) == 1'b0) |-> (R == ($past(A) + $past(B)))
    );

    // In subtract mode, R captures the prior cycle difference.
    check_subtraction_mode_result: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(C) == 1'b1) |-> (R == ($past(A) - $past(B)))
    );

    // Subtracting equal prior operands must produce zero.
    check_equal_operands_subtract_zero: assert property (
        @(posedge CLK) disable iff ($initstate)
        (($past(C) == 1'b1) && ($past(A) == $past(B))) |-> (R == 16'h0000)
    );

endmodule