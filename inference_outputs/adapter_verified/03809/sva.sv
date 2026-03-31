module adder_subtractor_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] result,
    input logic OVFL
);

// In add mode, result equals A + B (4-bit wrap).
    check_add_result: assert property (
        @(posedge CLK) (SUB == 1'b0) |-> (result == (A + B))
    );

// In subtract mode, result equals A - B (4-bit wrap).
    check_sub_result: assert property (
        @(posedge CLK) (SUB == 1'b1) |-> (result == (A - B))
    );

// OVFL is 0 when result[3] is 0 (no 4-bit carry).
    check_ovfl_low_when_no_carry: assert property (
        @(posedge CLK) (result[3] == 1'b0) |-> (OVFL == 1'b0)
    );

// OVFL is 1 when result[3] is 1 (4-bit carry).
    check_ovfl_high_when_carry: assert property (
        @(posedge CLK) (result[3] == 1'b1) |-> (OVFL == 1'b1)
    );

// In add mode, OVFL equals (A + B >= 16).
    check_add_ovfl_definition: assert property (
        @(posedge CLK) (SUB == 1'b0) |-> (OVFL == ((A + B) >= 4'd16))
    );

// In subtract mode, OVFL equals (A < B).
    check_sub_ovfl_definition: assert property (
        @(posedge CLK) (SUB == 1'b1) |-> (OVFL == (A < B))
    );

// OVFL is 0 when adding two 4-bit zeros.
    check_add_zero_case: assert property (
        @(posedge CLK) (SUB == 1'b0 && A == 4'd0 && B == 4'd0) |-> (OVFL == 1'b0)
    );

// OVFL is 1 when subtracting equal operands.
    check_sub_equal_operands: assert property (
        @(posedge CLK) (SUB == 1'b1 && A == B) |-> (OVFL == 1'b1)
    );

// In add mode, 0 - B equals (16 - B) (mod 16).
    check_add_zero_minus_b: assert property (
        @(posedge CLK) (SUB == 1'b0 && A == 4'd0) |-> (result == (4'd16 - B))
    );

// In subtract mode, A - 0 equals A (mod 16).
    check_sub_a_minus_zero: assert property (
        @(posedge CLK) (SUB == 1'b1 && B == 4'd0) |-> (result == A)
    );

endmodule
