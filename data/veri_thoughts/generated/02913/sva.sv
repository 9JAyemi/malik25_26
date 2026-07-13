module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // Combinational DUT, no reset/clock; assertions sample on clk.

    // sum[0] equals a[0] XOR b[0].
    check_sum0_is_a0_xor_b0: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // sum[1] equals a[0] XOR b[0] XOR b[1].
    check_sum1_prefix_xor: assert property (
        @(posedge clk) sum[1] == (a[0] ^ b[0] ^ b[1])
    );

    // sum[2] equals a[0] XOR b[0] XOR b[1] XOR b[2].
    check_sum2_prefix_xor: assert property (
        @(posedge clk) sum[2] == (a[0] ^ b[0] ^ b[1] ^ b[2])
    );

    // sum[3] equals a[0] XOR b[0] XOR b[1] XOR b[2] XOR b[3].
    check_sum3_prefix_xor: assert property (
        @(posedge clk) sum[3] == (a[0] ^ b[0] ^ b[1] ^ b[2] ^ b[3])
    );

    // cout equals (a[0] XOR b[0] XOR b[1] XOR b[2]) AND b[3].
    check_cout_def: assert property (
        @(posedge clk) cout == ((a[0] ^ b[0] ^ b[1] ^ b[2]) & b[3])
    );

    // sum[1] XOR sum[0] equals b[1].
    check_sum1_diff_b1: assert property (
        @(posedge clk) (sum[1] ^ sum[0]) == b[1]
    );

    // sum[2] XOR sum[1] equals b[2].
    check_sum2_diff_b2: assert property (
        @(posedge clk) (sum[2] ^ sum[1]) == b[2]
    );

    // sum[3] XOR sum[2] equals b[3].
    check_sum3_diff_b3: assert property (
        @(posedge clk) (sum[3] ^ sum[2]) == b[3]
    );

    // Outputs are independent of cin.
    check_cin_independence: assert property (
        @(posedge clk) ($changed(cin) && $stable(a) && $stable(b)) |-> ($stable(sum) && $stable(cout))
    );

    // a[1] has no effect on outputs.
    check_a1_unused: assert property (
        @(posedge clk) ($changed(a[1]) && $stable({a[0],a[2],a[3]}) && $stable(b)) |-> ($stable(sum) && $stable(cout))
    );

    // a[2] has no effect on outputs.
    check_a2_unused: assert property (
        @(posedge clk) ($changed(a[2]) && $stable({a[0],a[1],a[3]}) && $stable(b)) |-> ($stable(sum) && $stable(cout))
    );

    // a[3] has no effect on outputs.
    check_a3_unused: assert property (
        @(posedge clk) ($changed(a[3]) && $stable({a[0],a[1],a[2]}) && $stable(b)) |-> ($stable(sum) && $stable(cout))
    );

    // Changing only b[3] toggles sum[3] and leaves sum[2:0] unchanged.
    check_b3_affects_sum3_only: assert property (
        @(posedge clk) ($changed(b[3]) && $stable(a) && $stable(b[2:0])) |-> ($stable(sum[2:0]) && $changed(sum[3]))
    );

    // Changing only b[0] toggles all sum bits.
    check_b0_affects_all_sum: assert property (
        @(posedge clk) ($changed(b[0]) && $stable(a) && $stable(b[3:1])) |-> ($changed(sum[0]) && $changed(sum[1]) && $changed(sum[2]) && $changed(sum[3]))
    );

    // cout can only be 1 when b[3] is 1.
    check_cout_implies_b3: assert property (
        @(posedge clk) cout |-> b[3]
    );

endmodule