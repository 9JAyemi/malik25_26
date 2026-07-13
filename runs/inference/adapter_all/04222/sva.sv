module sky130_fd_sc_ls__ha_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B
);

    // COUT is the AND of A and B.
    check_cout_is_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

    // SUM is the XOR of A and B.
    check_sum_is_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // The outputs match the two-input half-adder equations.
    check_half_adder_equations: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B})
    );

    // Both low inputs produce both low outputs.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B) |-> (!COUT && !SUM)
    );

    // Both high inputs produce both high outputs.
    check_one_inputs: assert property (
        @(posedge clk) (A && B) |-> (COUT && SUM)
    );

    // Different inputs produce different outputs.
    check_different_inputs: assert property (
        @(posedge clk) (A ^ B) |-> (COUT ^ SUM)
    );

    // Equal inputs produce equal outputs.
    check_equal_inputs: assert property (
        @(posedge clk) !(A ^ B) |-> !(COUT ^ SUM)
    );

endmodule