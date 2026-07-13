module comparator_4bit_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic EQ
);

    // EQ must match the RTL compare equation.
    check_eq_matches_rtl_equation: assert property (
        @(posedge clk) EQ === ~(|(A ^ B))
    );

    // No bit differences must drive EQ high.
    check_no_bit_difference_sets_eq: assert property (
        @(posedge clk) (~(|(A ^ B))) |-> (EQ === 1'b1)
    );

    // Any bit difference must drive EQ low.
    check_any_bit_difference_clears_eq: assert property (
        @(posedge clk) (|(A ^ B)) |-> (EQ === 1'b0)
    );

    // EQ high implies the inputs have no differing bits.
    check_eq_high_implies_no_bit_difference: assert property (
        @(posedge clk) (EQ === 1'b1) |-> (~(|(A ^ B)))
    );

    // EQ low implies at least one input bit differs.
    check_eq_low_implies_bit_difference: assert property (
        @(posedge clk) (EQ === 1'b0) |-> (|(A ^ B))
    );

    // Stable inputs must keep EQ stable at sampled clock edges.
    check_stable_inputs_keep_eq_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(EQ)
    );

endmodule