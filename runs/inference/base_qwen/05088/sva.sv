module binary_adder_sva (
    input logic CLK,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VDD,
    input logic VSS
);
    // No reset signal is present in the RTL

    // The logic is purely combinational as it only uses logic gates without any sequential elements

    // Key signals and functional behaviors:
    // - SUM is the XOR of A, B, and CIN
    // - COUT is the OR of the ANDs of A, B, and CIN

    // Combinational logic assertions
    // SUM should be the XOR of A, B, and CIN
    sum_xor: assert property (
        @(posedge CLK) $rose(SUM) |-> (SUM == (A ^ B ^ CIN))
    );

    // COUT should be the OR of the ANDs of A, B, and CIN
    cout_or: assert property (
        @(posedge CLK) $rose(COUT) |-> (COUT == (A & B) | (A & CIN) | (B & CIN))
    );

    // If A, B, and CIN are all 0, SUM should be 0 and COUT should be 0
    zero_input: assert property (
        @(posedge CLK) (A == 1'b0) && (B == 1'b0) && (CIN == 1'b0) |-> (SUM == 1'b0) && (COUT == 1'b0)
    );

    // If A and B are 1 and CIN is 0, SUM should be 0 and COUT should be 1
    one_input_cin_zero: assert property (
        @(posedge CLK) (A == 1'b1) && (B == 1'b1) && (CIN == 1'b0) |-> (SUM == 1'b0) && (COUT == 1'b1)
    );

    // If A and B are 1 and CIN is 1, SUM should be 1 and COUT should be 1
    one_input_cin_one: assert property (
        @(posedge CLK) (A == 1'b1) && (B == 1'b1) && (CIN == 1'b1) |-> (SUM == 1'b1) && (COUT == 1'b1)
    );

    // If A is 1, B is 0, and CIN is 0, SUM should be 1 and COUT should be 0
    one_zero_zero: assert property (
        @(posedge CLK) (A == 1'b1) && (B == 1'b0) && (CIN == 1'b0) |-> (SUM == 1'b1) && (COUT == 1'b0)
    );

    // If A is 0, B is 1, and CIN is 0, SUM should be 1 and COUT should be 0
    zero_one_zero: assert property (
        @(posedge CLK) (A == 1'b0) && (B == 1'b1) && (CIN == 1'b0) |-> (SUM == 1'b1) && (COUT == 1'b0)
    );

    // If A is 0, B is 0, and CIN is 1, SUM should be 1 and COUT should be 0
    zero_zero_one: assert property (
        @(posedge CLK) (A == 1'b0) && (B == 1'b0) && (CIN == 1'b1) |-> (SUM == 1'b1) && (COUT == 1'b0)
    );

    // If A is 1, B is 1, and CIN is 0, SUM should be 0 and COUT should be 1
    one_one_zero: assert property (
        @(posedge CLK) (A == 1'b1) && (B == 1'b1) && (CIN == 1'b0) |-> (SUM == 1'b0) && (COUT == 1'b1)
    );

    // If A is 1, B is 0, and CIN is 1, SUM should be 0 and COUT should be 1
    one_zero_one: assert property (
        @(posedge CLK) (A == 1'b1) && (B == 1'b0) && (CIN == 1'b1) |-> (SUM == 1'b0) && (COUT == 1'b1)
    );

    // If A is 0, B is 1, and CIN is 1, SUM should be 0 and COUT should be 1
    zero_one_one: assert property (
        @(posedge CLK) (A == 1'b0) && (B == 1'b1) && (CIN == 1'b1) |-> (SUM == 1'b0) && (COUT == 1'b1)
    );

endmodule