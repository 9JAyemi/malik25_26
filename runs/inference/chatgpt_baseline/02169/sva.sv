module arithmetic_op_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] ctrl,
    input logic [7:0] result
);
    // Combinational DUT with no reset; assertions are sampled on CLK.

    // When ctrl==00, result equals a+b (8-bit wrap-around).
    check_add_function: assert property (
        @(posedge CLK) (ctrl == 2'b00) |-> (result == (a + b))
    );

    // When ctrl==01, result equals a-b (8-bit wrap-around).
    check_sub_function: assert property (
        @(posedge CLK) (ctrl == 2'b01) |-> (result == (a - b))
    );

    // When ctrl==10, result equals a^b.
    check_xor_function: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (result == (a ^ b))
    );

    // When ctrl==11, result is zero.
    check_default_zero: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (result == 8'h00)
    );

    // Result matches the full case-expression behavior.
    check_case_equivalence: assert property (
        @(posedge CLK)
        result == ((ctrl == 2'b00) ? (a + b) :
                   (ctrl == 2'b01) ? (a - b) :
                   (ctrl == 2'b10) ? (a ^ b) :
                                     8'h00)
    );

    // If inputs are stable across a cycle, result is stable too.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && $stable(ctrl)) |-> $stable(result)
    );

    // For XOR op, equal inputs yield zero.
    check_xor_equal_inputs_zero: assert property (
        @(posedge CLK) (ctrl == 2'b10 && (a == b)) |-> (result == 8'h00)
    );

    // For XOR op, XOR with zero b returns a.
    check_xor_with_zero_b_returns_a: assert property (
        @(posedge CLK) (ctrl == 2'b10 && (b == 8'h00)) |-> (result == a)
    );

    // For ADD op, adding zero b returns a.
    check_add_with_zero_b_returns_a: assert property (
        @(posedge CLK) (ctrl == 2'b00 && (b == 8'h00)) |-> (result == a)
    );

    // For SUB op, equal inputs yield zero.
    check_sub_equal_inputs_zero: assert property (
        @(posedge CLK) (ctrl == 2'b01 && (a == b)) |-> (result == 8'h00)
    );
endmodule