module nand_mux_4to1_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] S,
    input logic out
);

    // out matches the implemented NAND network.
    check_out_equation: assert property (
        @(posedge clk)
        out == (
            (~((~S[1]) & S[0])) &
            (~((~S[1]) & (~S[0]))) &
            (~((~(S[1] & S[0])) & A[0] & A[1])) &
            (~((~(S[1] & (~S[0]))) & A[1] & A[2]))
        )
    );

    // When S[1] is low, the output is forced low.
    check_s1_low_forces_out_low: assert property (
        @(posedge clk)
        (S[1] == 1'b0) |-> (out == 1'b0)
    );

    // For select 2'b10, out is the NAND of A[0] and A[1].
    check_sel_10_function: assert property (
        @(posedge clk)
        (S == 2'b10) |-> (out == ~(A[0] & A[1]))
    );

    // For select 2'b11, out is the NAND of A[1] and A[2].
    check_sel_11_function: assert property (
        @(posedge clk)
        (S == 2'b11) |-> (out == ~(A[1] & A[2]))
    );

    // With S[1] high and A[1] low, the output must be high.
    check_s1_high_a1_low_forces_out_high: assert property (
        @(posedge clk)
        ((S[1] == 1'b1) && (A[1] == 1'b0)) |-> (out == 1'b1)
    );

    // For select 2'b10, A[0] and A[1] both high drive out low.
    check_sel_10_pair_high_forces_out_low: assert property (
        @(posedge clk)
        ((S == 2'b10) && (A[0] == 1'b1) && (A[1] == 1'b1)) |-> (out == 1'b0)
    );

    // For select 2'b10, if A[0:1] are not both high then out is high.
    check_sel_10_pair_not_high_forces_out_high: assert property (
        @(posedge clk)
        ((S == 2'b10) && !(A[0] & A[1])) |-> (out == 1'b1)
    );

    // For select 2'b11, A[1] and A[2] both high drive out low.
    check_sel_11_pair_high_forces_out_low: assert property (
        @(posedge clk)
        ((S == 2'b11) && (A[1] == 1'b1) && (A[2] == 1'b1)) |-> (out == 1'b0)
    );

    // For select 2'b11, if A[1:2] are not both high then out is high.
    check_sel_11_pair_not_high_forces_out_high: assert property (
        @(posedge clk)
        ((S == 2'b11) && !(A[1] & A[2])) |-> (out == 1'b1)
    );

endmodule