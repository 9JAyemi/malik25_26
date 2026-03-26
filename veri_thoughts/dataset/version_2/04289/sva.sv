module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Full 5-bit output must match a + b + cin.
    check_sum_matches_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // The least-significant sum bit must be a[0] ^ b[0] ^ cin.
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Zero plus zero with no carry-in must produce zero.
    check_zero_inputs: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b0) |-> ({cout, sum} == 5'h00)
    );

    // Zero plus zero with carry-in must produce one.
    check_cin_only: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b1) |-> ({cout, sum} == 5'h01)
    );

    // Adding zero with no carry-in must pass through a.
    check_pass_through_a: assert property (
        @(posedge clk) (b == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, a})
    );

    // Adding zero with no carry-in must pass through b.
    check_pass_through_b: assert property (
        @(posedge clk) (a == 4'h0 && cin == 1'b0) |-> ({cout, sum} == {1'b0, b})
    );

    // Adding carry-in only must increment a.
    check_increment_a: assert property (
        @(posedge clk) (b == 4'h0 && cin == 1'b1) |-> ({cout, sum} == ({1'b0, a} + 5'h01))
    );

    // Adding carry-in only must increment b.
    check_increment_b: assert property (
        @(posedge clk) (a == 4'h0 && cin == 1'b1) |-> ({cout, sum} == ({1'b0, b} + 5'h01))
    );

    // Max inputs without carry-in must produce 0x1E.
    check_max_inputs_no_cin: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b0) |-> ({cout, sum} == 5'h1E)
    );

    // Max inputs with carry-in must produce 0x1F.
    check_max_inputs_with_cin: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> ({cout, sum} == 5'h1F)
    );

    // Carry-out must indicate 4-bit addition overflow.
    check_carry_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) >= 5'd16)
    );

endmodule