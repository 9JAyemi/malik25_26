module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] shift_amt,
    input logic mode,
    input logic [3:0] out
);

// Equal inputs force the output to zero.
    check_equal_forces_zero: assert property (
        @(posedge clk) (A == B) |-> (out == 4'h0)
    );

// Signed larger selects the shifted larger number.
    check_signed_larger_selects_shifted: assert property (
        @(posedge clk) ($signed(A) > $signed(B)) |-> (out == ((mode) ? (A >> shift_amt) : (A >>> shift_amt)))
    );

// Signed smaller selects the smaller number.
    check_signed_smaller_selects_smaller: assert property (
        @(posedge clk) ($signed(A) < $signed(B)) |-> (out == B)
    );

// With no signed comparison, the output matches B.
    check_no_signed_comparison_selects_b: assert property (
        @(posedge clk) !($signed(A) > $signed(B)) && !($signed(A) < $signed(B)) |-> (out == B)
    );

// In mode 0, the larger number is zero-extended.
    check_mode0_zero_extends_larger: assert property (
        @(posedge clk) (mode == 1'b0) |-> (out == ((A >> shift_amt) & 4'hF))
    );

// In mode 1, the larger number is sign-extended.
    check_mode1_sign_extends_larger: assert property (
        @(posedge clk) (mode == 1'b1) |-> (out == (A >> shift_amt))
    );

endmodule
