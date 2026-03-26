module sky130_fd_sc_ms__fah_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

    // SUM is the XOR of A, B, and CI.
    check_sum_xor: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT is high when at least two inputs are high.
    check_cout_majority: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // The outputs match the 2-bit binary sum of the inputs.
    check_full_add_value: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CI) |-> ((SUM == 1'b0) && (COUT == 1'b0))
    );

    // Exactly one high input produces SUM high and COUT low.
    check_single_one_case: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI))
        |-> ((SUM == 1'b1) && (COUT == 1'b0))
    );

    // Exactly two high inputs produce SUM low and COUT high.
    check_double_one_case: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI))
        |-> ((SUM == 1'b0) && (COUT == 1'b1))
    );

    // All-one inputs produce SUM high and COUT high.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CI) |-> ((SUM == 1'b1) && (COUT == 1'b1))
    );

endmodule