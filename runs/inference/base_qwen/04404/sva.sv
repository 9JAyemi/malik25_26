module or3_2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic X
);
    // No clock or reset signals present in the RTL

    // Combinational logic: X is determined by A, B, and C
    // X = (A & B) | (A & C) | (B & C)
    // This logic is always active, so we use @(posedge clk) to clock the assertion

    // Property to check the correct behavior of the OR3_2 module
    // Ensure that X is correctly computed based on A, B, and C
    check_or3_2: assert property (
        @(posedge clk) disable iff (1'b0) (X == (A & B) | (A & C) | (B & C))
    ) else $error("OR3_2 output X is incorrect");

endmodule