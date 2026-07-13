module addsub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT,
    input logic COUT,
    input logic [3:0] B_INV,
    input logic [3:0] ADD,
    input logic SUB_NEG
);

    // B_INV is the bitwise inverse of B.
    check_b_inv_complement: assert property (
        @(posedge clk) B_INV == ~B
    );

    // ADD uses A+B when SUB is low.
    check_add_uses_a_plus_b_in_add_mode: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (ADD == (A + B))
    );

    // ADD uses A+~B when SUB is high.
    check_add_uses_a_plus_inverted_b_in_sub_mode: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (ADD == (A + B_INV))
    );

    // SUB_NEG matches the MSB of ADD.
    check_sub_neg_is_add_msb: assert property (
        @(posedge clk) SUB_NEG == ADD[3]
    );

    // COUT is driven from SUB_NEG.
    check_cout_matches_sub_neg: assert property (
        @(posedge clk) COUT == SUB_NEG
    );

    // OUT follows ADD in add mode.
    check_out_follows_add_in_add_mode: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (OUT == ADD)
    );

    // OUT matches A+B in add mode.
    check_out_matches_sum_in_add_mode: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (OUT == (A + B))
    );

    // COUT matches OUT[3] in add mode.
    check_cout_matches_out_msb_in_add_mode: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (COUT == OUT[3])
    );

    // OUT follows B_INV+1 in subtract mode.
    check_out_follows_b_inv_plus_one_in_sub_mode: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (OUT == (B_INV + 4'd1))
    );

    // OUT matches ~B+1 in subtract mode.
    check_out_matches_twos_complement_b_in_sub_mode: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (OUT == ((~B) + 4'd1))
    );

endmodule