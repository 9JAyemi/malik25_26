module binary_adder_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VDD,
    input logic VSS
);

// SUM is the XOR of A, B, and inverted CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

// COUT is the majority function of A, B, and inverted CIN.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

// With CIN low, SUM is the XOR of A and B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (SUM == (A ^ B))
    );

// With CIN low, COUT is A AND B.
    check_cout_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (COUT == (A & B))
    );

// With CIN high, SUM is the inverse of A XOR B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) CIN |-> (SUM == ~(A ^ B))
    );

// With CIN high, COUT is A OR B.
    check_cout_when_cin_high: assert property (
        @(posedge clk) CIN |-> (COUT == (A | B))
    );

// All-zero inputs produce zero SUM and zero COUT.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B && !CIN) |-> (!SUM && !COUT)
    );

// All-one inputs produce one SUM and one COUT.
    check_all_one_inputs: assert property (
        @(posedge clk) (A && B && CIN) |-> (SUM && COUT)
    );

// Exactly one high input produces one SUM and zero COUT.
    check_one_hot_inputs: assert property (
        @(posedge clk)
        ((A && !B && !CIN) || (!A && B && !CIN) || (!A && !B && CIN))
        |-> (SUM && !COUT)
    );

// Exactly two high inputs produce zero SUM and one COUT.
    check_two_hot_inputs: assert property (
        @(posedge clk)
        ((A && B && !CIN) || (A && !B && CIN) || (!A && B && CIN))
        |-> (!SUM && COUT)
    );

endmodule
