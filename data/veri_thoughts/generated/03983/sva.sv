module sky130_fd_sc_ms__fahcon_sva (
    input logic clk,
    input logic COUT_N,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the parity of A, B, and CI.
    check_sum_parity: assert property (
        @(posedge clk) (SUM == (A ^ B ^ CI))
    );

    // COUT_N matches the implemented OR-of-NOR carry complement logic.
    check_cout_n_nor_or_function: assert property (
        @(posedge clk) (COUT_N == ((~(A | B)) | (~(A | CI)) | (~(B | CI))))
    );

    // All-zero inputs produce SUM low and COUT_N high.
    check_zero_input_case: assert property (
        @(posedge clk)
        ((A == 1'b0) && (B == 1'b0) && (CI == 1'b0))
        |-> ((SUM == 1'b0) && (COUT_N == 1'b1))
    );

    // Exactly one high input produces SUM high and COUT_N high.
    check_single_high_case: assert property (
        @(posedge clk)
        (((A == 1'b1) && (B == 1'b0) && (CI == 1'b0)) ||
         ((A == 1'b0) && (B == 1'b1) && (CI == 1'b0)) ||
         ((A == 1'b0) && (B == 1'b0) && (CI == 1'b1)))
        |-> ((SUM == 1'b1) && (COUT_N == 1'b1))
    );

    // Exactly two high inputs produce SUM low and COUT_N low.
    check_double_high_case: assert property (
        @(posedge clk)
        (((A == 1'b1) && (B == 1'b1) && (CI == 1'b0)) ||
         ((A == 1'b1) && (B == 1'b0) && (CI == 1'b1)) ||
         ((A == 1'b0) && (B == 1'b1) && (CI == 1'b1)))
        |-> ((SUM == 1'b0) && (COUT_N == 1'b0))
    );

    // All-high inputs produce SUM high and COUT_N low.
    check_all_high_case: assert property (
        @(posedge clk)
        ((A == 1'b1) && (B == 1'b1) && (CI == 1'b1))
        |-> ((SUM == 1'b1) && (COUT_N == 1'b0))
    );

endmodule