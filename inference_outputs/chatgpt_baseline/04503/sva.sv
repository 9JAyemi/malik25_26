module sky130_fd_sc_hd__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // Combined outputs match 1-bit addition.
    check_full_adder_result: assert property (
        @(posedge clk)
        ({COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI}))
    );

    // SUM is the XOR of the three inputs.
    check_sum_parity: assert property (
        @(posedge clk)
        (SUM == (A ^ B ^ CI))
    );

    // COUT is high when any two inputs are high.
    check_cout_majority: assert property (
        @(posedge clk)
        (COUT == ((A & B) | (A & CI) | (B & CI)))
    );

    // All-zero inputs produce zero outputs.
    check_all_zero_case: assert property (
        @(posedge clk)
        ((!A && !B && !CI) |-> (!COUT && !SUM))
    );

    // Exactly one high input produces SUM only.
    check_one_high_case: assert property (
        @(posedge clk)
        (((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI)) |-> (SUM && !COUT))
    );

    // Exactly two high inputs produce COUT only.
    check_two_high_case: assert property (
        @(posedge clk)
        (((A && B && !CI) || (A && !B && CI) || (!A && B && CI)) |-> (!SUM && COUT))
    );

    // All-one inputs produce both SUM and COUT.
    check_all_one_case: assert property (
        @(posedge clk)
        ((A && B && CI) |-> (SUM && COUT))
    );

endmodule