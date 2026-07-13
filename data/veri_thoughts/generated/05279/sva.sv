module adder_4bit_carry_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Combined output must equal a + b + cin.
    check_full_addition_result: assert property (
        @($global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0, cin})
    );

    // The least-significant sum bit must be the XOR of the input LSBs and cin.
    check_lsb_sum_xor: assert property (
        @($global_clock) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Adding zero with no carry-in must pass through a.
    check_b_zero_passes_a: assert property (
        @($global_clock) (b == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero with no carry-in must pass through b.
    check_a_zero_passes_b: assert property (
        @($global_clock) (a == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, b})
    );

    // Zero plus zero with carry-in must produce 1.
    check_cin_only_increment: assert property (
        @($global_clock) (a == 4'h0 && b == 4'h0 && cin == 1'b1) |-> ({cout, sum} == 5'h01)
    );

    // Totals below 16 must not assert carry-out.
    check_no_overflow_clears_cout: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b} + {4'b0, cin}) < 5'd16) |-> (cout == 1'b0)
    );

    // Totals of 16 or more must assert carry-out.
    check_overflow_sets_cout: assert property (
        @($global_clock) (({1'b0, a} + {1'b0, b} + {4'b0, cin}) >= 5'd16) |-> (cout == 1'b1)
    );

    // The maximum input combination must produce 31.
    check_maximum_input_result: assert property (
        @($global_clock) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> ({cout, sum} == 5'h1F)
    );

    // A carry generated only by cin at the boundary must be reflected in the output.
    check_cin_boundary_carry: assert property (
        @($global_clock) (a == 4'hF && b == 4'h0 && cin == 1'b1) |-> ({cout, sum} == 5'h10)
    );

endmodule