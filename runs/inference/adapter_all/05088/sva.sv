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

    // SUM matches the XOR of A, B, and inverted CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

    // COUT matches the majority function of A, B, and inverted CIN.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

    // With CIN low, SUM is the XOR of A and B.
    check_sum_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (SUM == (A ^ B))
    );

    // With CIN high, SUM is the inversion of A XOR B.
    check_sum_when_cin_high: assert property (
        @(posedge clk) CIN |-> (SUM == ~(A ^ B))
    );

    // With CIN low, COUT reduces to A OR B.
    check_cout_when_cin_low: assert property (
        @(posedge clk) !CIN |-> (COUT == (A | B))
    );

    // With CIN high, COUT reduces to A AND B.
    check_cout_when_cin_high: assert property (
        @(posedge clk) CIN |-> (COUT == (A & B))
    );

    // All-zero inputs produce zero outputs.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B && !CIN) |-> (!SUM && !COUT)
    );

    // All-one inputs produce inverted SUM and COUT.
    check_all_one_inputs: assert property (
        @(posedge clk) (A && B && CIN) |-> (SUM && !COUT)
    );

    // With CIN low and A equal to B, both outputs are low.
    check_equal_ab_cin_low: assert property (
        @(posedge clk) (!CIN && (A == B)) |-> (!SUM && !COUT)
    );

    // With CIN high and A equal to B, both outputs are high.
    check_equal_ab_cin_high: assert property (
        @(posedge clk) (CIN && (A == B)) |-> (SUM && COUT)
    );

endmodule