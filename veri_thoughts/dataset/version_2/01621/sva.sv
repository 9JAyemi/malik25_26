module top_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // No clock or reset in RTL; pure combinational ripple-carry adder.
    // Checker uses external clk for sampling; no disable iff.
    // Ports: a[3:0], b[3:0], cin -> sum[3:0], cout.

    // Sum and carry-out equal zero-extended addition of inputs.
    check_full_sum: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Bit 0 sum equals a0 ^ b0 ^ cin.
    check_sum0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum equals a1 ^ b1 ^ carry0.
    check_sum1_xor_with_carry0: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))))
    );

    // Bit 2 sum equals a2 ^ b2 ^ carry1.
    check_sum2_xor_with_carry1: assert property (
        @(posedge clk) sum[2] == (
            a[2] ^ b[2] ^
            ((a[1] & b[1]) | (((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1])))
        )
    );

    // Bit 3 sum equals a3 ^ b3 ^ carry2.
    check_sum3_xor_with_carry2: assert property (
        @(posedge clk) sum[3] == (
            a[3] ^ b[3] ^
            (
                (a[2] & b[2]) |
                (
                    ((a[1] & b[1]) | (((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1])))
                    & (a[2] ^ b[2])
                )
            )
        )
    );

    // Carry-out equals carry3 from the final full adder stage.
    check_cout_carry3: assert property (
        @(posedge clk) cout == (
            (a[3] & b[3]) |
            (
                (
                    (a[2] & b[2]) |
                    (
                        ((a[1] & b[1]) | (((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) & (a[1] ^ b[1])))
                        & (a[2] ^ b[2])
                    )
                )
                & (a[3] ^ b[3])
            )
        )
    );

    // When a=0 and b=0, sum mirrors cin on bit0 and cout is 0.
    check_zero_inputs_behavior: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000)) |-> (sum == {3'b000, cin}) && (cout == 1'b0)
    );

    // When a=15, b=15, cin=1, result is 31 (5'b11111).
    check_all_ones_plus_one: assert property (
        @(posedge clk) ((a == 4'hF) && (b == 4'hF) && (cin == 1'b1)) |-> ({cout, sum} == 5'b11111)
    );

    // With a=0 and cin=0, output equals b and cout is 0.
    check_add_b_when_a_zero_cin0: assert property (
        @(posedge clk) ((a == 4'b0000) && (cin == 1'b0)) |-> (sum == b) && (cout == 1'b0)
    );

    // With b=0 and cin=0, output equals a and cout is 0.
    check_add_a_when_b_zero_cin0: assert property (
        @(posedge clk) ((b == 4'b0000) && (cin == 1'b0)) |-> (sum == a) && (cout == 1'b0)
    );

endmodule