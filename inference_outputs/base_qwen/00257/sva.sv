module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    output logic [3:0] SUM,
    output logic COUT
);
    // Combinational logic: SUM and COUT are determined by A, B, and CIN
    // No clock or reset signals are present in the RTL
    // Therefore, we use @(posedge clk) to clock the assertions

    // SUM is the XOR of A, B, and CIN
    sum_correct: assert property (
        @(posedge clk) disable iff (1'b0) SUM == (A ^ B ^ CIN)
    ) else $error("SUM is incorrect");

    // COUT is the OR of the ANDs of A and B, B and CIN, and CIN and A
    cout_correct: assert property (
        @(posedge clk) disable iff (1'b0) COUT == ((A & B) | (B & CIN) | (CIN & A))
    ) else $error("COUT is incorrect");

endmodule