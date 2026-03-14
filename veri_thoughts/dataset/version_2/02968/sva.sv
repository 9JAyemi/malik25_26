module adder_with_carry_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);
    // DUT is a purely combinational ripple-carry adder with no clock/reset.
    // Assertions are clocked on external CLK; no disable iff since no reset in RTL.

    // Expected 5-bit result from arithmetic addition
    logic [4:0] expected;
    assign expected = a + b + cin;

    // Propagate/Generate and ripple-carry computation from inputs only
    logic p0, p1, p2, p3;
    logic g0, g1, g2, g3;
    logic c1_e, c2_e, c3_e, c4_e;
    logic [3:0] s_e;

    assign p0 = a[0] ^ b[0];
    assign p1 = a[1] ^ b[1];
    assign p2 = a[2] ^ b[2];
    assign p3 = a[3] ^ b[3];

    assign g0 = a[0] & b[0];
    assign g1 = a[1] & b[1];
    assign g2 = a[2] & b[2];
    assign g3 = a[3] & b[3];

    assign c1_e = g0 | (p0 & cin);
    assign s_e[0] = p0 ^ cin;

    assign c2_e = g1 | (p1 & c1_e);
    assign s_e[1] = p1 ^ c1_e;

    assign c3_e = g2 | (p2 & c2_e);
    assign s_e[2] = p2 ^ c2_e;

    assign c4_e = g3 | (p3 & c3_e);
    assign s_e[3] = p3 ^ c3_e;

    // Sum+carry equals 5-bit arithmetic addition of inputs.
    check_addition_equivalence: assert property (
        @(posedge CLK) {cout, sum} == expected
    );

    // LSB sum equals XOR of a[0], b[0], and cin.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit1 sum equals XOR of a[1], b[1], and computed c1.
    check_sum_bit1_ripple: assert property (
        @(posedge CLK) sum[1] == (a[1] ^ b[1] ^ c1_e)
    );

    // Bit2 sum equals XOR of a[2], b[2], and computed c2.
    check_sum_bit2_ripple: assert property (
        @(posedge CLK) sum[2] == (a[2] ^ b[2] ^ c2_e)
    );

    // Bit3 sum equals XOR of a[3], b[3], and computed c3.
    check_sum_bit3_ripple: assert property (
        @(posedge CLK) sum[3] == (a[3] ^ b[3] ^ c3_e)
    );

    // Carry-out equals computed ripple carry c4.
    check_carry_out_ripple: assert property (
        @(posedge CLK) cout == c4_e
    );

    // Sum vector matches per-bit ripple computation.
    check_sum_vector_matches_ripple: assert property (
        @(posedge CLK) sum == s_e
    );

    // Outputs remain stable when inputs are stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge CLK) $stable({a,b,cin}) |-> $stable({sum,cout})
    );

    // Zero inputs with cin=0 produce zero sum and no carry.
    check_zero_plus_zero_no_carry: assert property (
        @(posedge CLK) (a == 4'b0000) && (b == 4'b0000) && (cin == 1'b0) |-> (sum == 4'b0000) && (cout == 1'b0)
    );

    // Max + Max + 1 yields sum=0xF and cout=1 (31 decimal).
    check_saturation_case_max_plus_one: assert property (
        @(posedge CLK) (a == 4'hF) && (b == 4'hF) && (cin == 1'b1) |-> (sum == 4'hF) && (cout == 1'b1)
    );

    // 0xF + 0 + cin=1 yields sum=0 and cout=1 (carry from LSB ripple).
    check_wrap_case_f_plus_one: assert property (
        @(posedge CLK) (a == 4'hF) && (b == 4'h0) && (cin == 1'b1) |-> (sum == 4'h0) && (cout == 1'b1)
    );
endmodule