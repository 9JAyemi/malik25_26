module eightbit_alu_sva (
    input logic clk,
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic [2:0] sel,
    input logic signed [7:0] f,
    input logic ovf,
    input logic zero
);

    // RTL is purely combinational with no reset; clk is a sampling clock.

    // Add mode drives the sum, signed overflow, and zero low.
    check_add_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b000) |-> ((f == (a + b)) &&
                             (ovf == (~(a[7] ^ b[7]) & (a[7] ^ f[7]))) &&
                             (zero == 1'b0))
    );

    // Invert mode drives bitwise not of b and keeps flags low.
    check_invert_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b001) |-> ((f == (~b)) &&
                             (ovf == 1'b0) &&
                             (zero == 1'b0))
    );

    // AND mode drives a & b and keeps flags low.
    check_and_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b010) |-> ((f == (a & b)) &&
                             (ovf == 1'b0) &&
                             (zero == 1'b0))
    );

    // OR mode drives a | b and keeps flags low.
    check_or_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b011) |-> ((f == (a | b)) &&
                             (ovf == 1'b0) &&
                             (zero == 1'b0))
    );

    // Arithmetic right shift mode drives a >>> 1 and keeps flags low.
    check_arith_right_shift_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b100) |-> ((f == (a >>> 1)) &&
                             (ovf == 1'b0) &&
                             (zero == 1'b0))
    );

    // Arithmetic left shift mode drives a <<< 1 and keeps flags low.
    check_arith_left_shift_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b101) |-> ((f == (a <<< 1)) &&
                             (ovf == 1'b0) &&
                             (zero == 1'b0))
    );

    // Equal-compare mode drives zero from a == b and clears f and ovf.
    check_equal_compare_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b110) |-> ((f == 8'sd0) &&
                             (ovf == 1'b0) &&
                             (zero == (a == b)))
    );

    // Not-equal-compare mode drives zero from a != b and clears f and ovf.
    check_not_equal_compare_mode_outputs: assert property (
        @(posedge clk)
        (sel == 3'b111) |-> ((f == 8'sd0) &&
                             (ovf == 1'b0) &&
                             (zero == (a != b)))
    );

    // Overflow can only be asserted in add mode.
    check_overflow_only_in_add_mode: assert property (
        @(posedge clk)
        ovf |-> (sel == 3'b000)
    );

    // A high zero flag must come from the active compare mode result.
    check_zero_high_matches_compare_mode: assert property (
        @(posedge clk)
        zero |-> (((sel == 3'b110) && (a == b)) ||
                  ((sel == 3'b111) && (a != b)))
    );

endmodule