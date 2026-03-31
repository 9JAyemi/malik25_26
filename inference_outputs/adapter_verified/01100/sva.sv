module Approx_adder_sva (
    input logic clk,
    input logic add_sub,
    input logic [W-1:0] in1,
    input logic [W-1:0] in2,
    input logic [W:0] res
);

// No reset in RTL; sample on clk.

    // In add mode, res equals in1 + in2 (zero-extended to W+1 bits).
    check_add_mode_result: assert property (
        @(posedge clk) !add_sub |-> (res == {1'b0, in1} + {1'b0, in2})
    );

// In subtract mode, res equals in1 - in2 (zero-extended to W+1 bits).
    check_sub_mode_result: assert property (
        @(posedge clk) add_sub |-> (res == {1'b0, in1} - {1'b0, in2})
    );

// In add mode, the upper bit of res matches the addition carry.
    check_add_carry_bit: assert property (
        @(posedge clk) !add_sub |-> (res[W] == (in1[W-1:0] + in2[W-1:0] >= 16'h1000))
    );

// In subtract mode, the upper bit of res matches the subtraction borrow.
    check_sub_borrow_bit: assert property (
        @(posedge clk) add_sub |-> (res[W] == (in1[W-1:0] < in2[W-1:0]))
    );

// In add mode, the lower 16 bits of res match the low 16 bits of the sum.
    check_add_lower_bits: assert property (
        @(posedge clk) !add_sub |-> (res[W-1:0] == (in1[W-1:0] + in2[W-1:0]))
    );

// In subtract mode, the lower 16 bits of res match the low 16 bits of the difference.
    check_sub_lower_bits: assert property (
        @(posedge clk) add_sub |-> (res[W-1:0] == (in1[W-1:0] - in2[W-1:0]))
    );

// In add mode, zero plus zero yields zero.
    check_add_zero_plus_zero: assert property (
        @(posedge clk) (!add_sub && (in1 == 16'h0000) && (in2 == 16'h0000)) |-> (res == 17'h00000)
    );

// In subtract mode, zero minus zero yields zero.
    check_sub_zero_minus_zero: assert property (
        @(posedge clk) (add_sub && (in1 == 16'h0000) && (in2 == 16'h0000)) |-> (res == 17'h00000)
    );

// In add mode, adding zero on in1 passes in2 through with zero carry.
    check_add_zero_in1_passthrough: assert property (
        @(posedge clk) (!add_sub && (in1 == 16'h0000)) |-> (res == {1'b0, in2})
    );

// In subtract mode, subtracting zero on in2 passes in1 through with zero borrow.
    check_sub_zero_in2_passthrough: assert property (
        @(posedge clk) (add_sub && (in2 == 16'h0000)) |-> (res == {1'b0, in1})
    );

endmodule
