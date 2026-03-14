module four_bit_adder_sva (
    input  logic        clk,   // sampling clock for assertions (RTL has no clock)
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    input  logic        cin,
    input  logic [3:0]  sum,
    input  logic        cout
);
    // RTL is purely combinational with no reset; wrapper adds clk for property sampling.

    // sum[0] implements (a0 ^ b0) ^ cin.
    check_sum0_def: assert property (
        @(posedge clk) sum[0] == ((a[0] ^ b[0]) ^ cin)
    );

    // sum[1] implements (a1 ^ b1) ^ (a0 & b0).
    check_sum1_def: assert property (
        @(posedge clk) sum[1] == ((a[1] ^ b[1]) ^ (a[0] & b[0]))
    );

    // sum[2] implements (a2 ^ b2) ^ (a1 & b1).
    check_sum2_def: assert property (
        @(posedge clk) sum[2] == ((a[2] ^ b[2]) ^ (a[1] & b[1]))
    );

    // sum[3] implements (a3 ^ b3) ^ (a2 & b2).
    check_sum3_def: assert property (
        @(posedge clk) sum[3] == ((a[3] ^ b[3]) ^ (a[2] & b[2]))
    );

    // cout implements (a2 ^ b2) | (a3 ^ b3).
    check_cout_def: assert property (
        @(posedge clk) cout == ((a[2] ^ b[2]) | (a[3] ^ b[3]))
    );

    // When a0 equals b0, sum[0] equals cin.
    sum0_when_equal_inputs0: assert property (
        @(posedge clk) (a[0] == b[0]) |-> (sum[0] == cin)
    );

    // When a0 differs from b0, sum[0] equals ~cin.
    sum0_when_diff_inputs0: assert property (
        @(posedge clk) (a[0] != b[0]) |-> (sum[0] == ~cin)
    );

    // When a1 equals b1, sum[1] equals (a0 & b0).
    sum1_when_equal_inputs1: assert property (
        @(posedge clk) (a[1] == b[1]) |-> (sum[1] == (a[0] & b[0]))
    );

    // When a1 differs from b1, sum[1] equals ~(a0 & b0).
    sum1_when_diff_inputs1: assert property (
        @(posedge clk) (a[1] != b[1]) |-> (sum[1] == ~(a[0] & b[0]))
    );

    // If upper-bit pairs are equal, cout must be 0.
    cout_zero_when_top_pairs_equal: assert property (
        @(posedge clk) ((a[2] == b[2]) && (a[3] == b[3])) |-> (cout == 1'b0)
    );

    // If any upper-bit pair differs, cout must be 1.
    cout_one_when_any_top_pair_diff: assert property (
        @(posedge clk) ((a[2] != b[2]) || (a[3] != b[3])) |-> (cout == 1'b1)
    );

    // sum[0] changes only with a0, b0, or cin.
    sum0_dep_stability: assert property (
        @(posedge clk) $stable({a[0], b[0], cin}) |-> $stable(sum[0])
    );

    // sum[1] changes only with a1, b1, a0, or b0.
    sum1_dep_stability: assert property (
        @(posedge clk) $stable({a[1], b[1], a[0], b[0]}) |-> $stable(sum[1])
    );

    // sum[2] changes only with a2, b2, a1, or b1.
    sum2_dep_stability: assert property (
        @(posedge clk) $stable({a[2], b[2], a[1], b[1]}) |-> $stable(sum[2])
    );

    // sum[3] changes only with a3, b3, a2, or b2.
    sum3_dep_stability: assert property (
        @(posedge clk) $stable({a[3], b[3], a[2], b[2]}) |-> $stable(sum[3])
    );

    // cout changes only with a2, b2, a3, or b3.
    cout_dep_stability: assert property (
        @(posedge clk) $stable({a[2], b[2], a[3], b[3]}) |-> $stable(cout)
    );

endmodule