module addsub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sub,
    input logic [3:0] S
);

    // No reset in RTL; this combinational logic is sampled on clk.

    // Output matches the selected add/sub result.
    check_function_select: assert property (
        @(posedge clk) (S == (sub ? (A + (~B + 4'b0001)) : (A + B)))
    );

    // In add mode, S is A plus B.
    check_add_mode_result: assert property (
        @(posedge clk) (!sub) |-> (S == (A + B))
    );

    // In subtract mode, S is A plus two's complement of B.
    check_sub_mode_result: assert property (
        @(posedge clk) sub |-> (S == (A + (~B + 4'b0001)))
    );

    // B equal to zero leaves A unchanged in either mode.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (B == 4'h0) |-> (S == A)
    );

    // In add mode, zero on A passes B through.
    check_add_zero_a_passthrough: assert property (
        @(posedge clk) ((!sub) && (A == 4'h0)) |-> (S == B)
    );

    // Subtracting equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (sub && (A == B)) |-> (S == 4'h0)
    );

    // Subtraction result plus B reconstructs A modulo 16.
    check_sub_inverse_relation: assert property (
        @(posedge clk) sub |-> ((S + B) == A)
    );

    // Subtracting from zero yields the two's complement of B.
    check_sub_from_zero_twos_complement: assert property (
        @(posedge clk) (sub && (A == 4'h0)) |-> (S == (~B + 4'b0001))
    );

endmodule