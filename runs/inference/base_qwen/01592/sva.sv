module full_adder_sva (
    input logic A,
    input logic B,
    input logic CI,
    output logic SUM,
    output logic COUT
);
    // Combinational logic, so use @(posedge clk)
    // SUM is the XOR of A, B, and CI
    sum_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (SUM == (A ^ B ^ CI))
    );
    // COUT is the OR of the ANDs of A and B, B and CI, and CI and A
    cout_correct: assert property (
        @(posedge clk) disable iff (!reset_n) (COUT == ((A & B) | (B & CI) | (CI & A)))
    );
endmodule