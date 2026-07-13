module sky130_fd_sc_hd__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

// SUM is the 3-input XOR of A, B, and CI.
    check_sum_is_xor3: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

// COUT is the majority function of A, B, and CI.
    check_cout_is_majority: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

// All-zero inputs produce zero SUM and zero COUT.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

// Exactly one high input produces SUM high and COUT low.
    check_one_hot_inputs: assert property (
        @(posedge clk)
        ((A && !B && !CI) || (!A && B && !CI) || (!A && !B && CI))
        |-> (SUM && !COUT)
    );

// Exactly two high inputs produce SUM low and COUT high.
    check_two_hot_inputs: assert property (
        @(posedge clk)
        ((A && B && !CI) || (A && !B && CI) || (!A && B && CI))
        |-> (!SUM && COUT)
    );

// All-high inputs produce SUM high and COUT high.
    check_all_high_inputs: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && COUT)
    );

endmodule
