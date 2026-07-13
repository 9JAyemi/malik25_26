module top_module_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum,
    input logic carry_out
);
    // Notes: No clock/reset in RTL; combinational logic; behavior: {carry_out,sum} = A + B.

    // Outputs equal the 5-bit sum of inputs.
    check_add_equivalence: assert property (
        @(posedge CLK) {carry_out, sum} == ({1'b0, A} + {1'b0, B})
    );

    // Sum equals low 4 bits of the 5-bit total.
    check_sum_low_nibble: assert property (
        @(posedge CLK) sum == ({1'b0, A} + {1'b0, B})[3:0]
    );

    // Carry equals MSB of the 5-bit total.
    check_carry_msb: assert property (
        @(posedge CLK) carry_out == ({1'b0, A} + {1'b0, B})[4]
    );

    // No carry when total is less than 16.
    check_no_carry_when_total_lt_16: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B}) < 5'd16) |-> (carry_out == 1'b0)
    );

    // Carry asserted when total is 16 or more.
    check_carry_when_total_ge_16: assert property (
        @(posedge CLK) (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> (carry_out == 1'b1)
    );

    // When carry occurs, sum wraps by subtracting 16.
    check_sum_wrap_on_carry: assert property (
        @(posedge CLK) carry_out |-> (sum == (({1'b0, A} + {1'b0, B}) - 5'd16))
    );

    // Adding zero on A side passes B through with no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 4'd0) |-> (sum == B) && (carry_out == 1'b0)
    );

    // Adding zero on B side passes A through with no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 4'd0) |-> (sum == A) && (carry_out == 1'b0)
    );

    // Boundary case: 15 + 15 = 30 => carry=1, sum=14.
    check_boundary_15_plus_15: assert property (
        @(posedge CLK) (A == 4'd15 && B == 4'd15) |-> (carry_out == 1'b1 && sum == 4'd14)
    );

    // Outputs remain stable across cycles if inputs are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(sum) && $stable(carry_out)
    );
endmodule