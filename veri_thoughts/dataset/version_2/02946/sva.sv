module subtract_8bit_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] difference
);
    // difference implements 8-bit subtraction A - B
    check_difference_function: assert property (
        @(posedge clk) difference == (A - B)
    );

    // If inputs are stable, output remains stable
    check_stability: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(difference)
    );

    // When A equals B, the difference is zero
    check_zero_when_equal: assert property (
        @(posedge clk) (A == B) |-> (difference == 8'h00)
    );

    // When B is zero, the difference equals A
    check_b_zero_passthrough: assert property (
        @(posedge clk) (B == 8'h00) |-> (difference == A)
    );

    // When A is zero, the difference equals two's complement of B
    check_a_zero_twos_complement: assert property (
        @(posedge clk) (A == 8'h00) |-> (difference == (~B + 8'h01))
    );

    // Subtracting 8'hFF equals adding 1 (mod 256)
    check_sub_ff_is_inc: assert property (
        @(posedge clk) (B == 8'hFF) |-> (difference == (A + 8'h01))
    );

    // (A - B) + B recovers A (mod 256)
    check_add_back_b_recovers_a: assert property (
        @(posedge clk) (difference + B) == A
    );

    // A - (A - B) recovers B (mod 256)
    check_reverse_sub_recovers_b: assert property (
        @(posedge clk) (A - difference) == B
    );

    // If A increments by 1 and B is stable, difference increments by 1
    check_a_inc_updates_diff: assert property (
        @(posedge clk) ($stable(B) && (A == $past(A) + 8'h01)) |-> (difference == $past(difference) + 8'h01)
    );

    // If B increments by 1 and A is stable, difference decrements by 1
    check_b_inc_updates_diff: assert property (
        @(posedge clk) ($stable(A) && (B == $past(B) + 8'h01)) |-> (difference == $past(difference) - 8'h01)
    );
endmodule