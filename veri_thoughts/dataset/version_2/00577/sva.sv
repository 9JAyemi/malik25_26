module sky130_fd_sc_hd__fa_sva (
    input  logic clk,   // property clock
    input  logic COUT,
    input  logic SUM,
    input  logic A,
    input  logic B,
    input  logic CIN
);
    // COUT implements majority-of-three: (A&B) | (A&CIN) | (B&CIN).
    check_cout_majority: assert property (
        @(posedge clk) disable iff (1'b0)
        COUT == ((A & B) | (A & CIN) | (B & CIN))
    );

    // SUM is odd parity of inputs: A ^ B ^ CIN.
    check_sum_parity: assert property (
        @(posedge clk) disable iff (1'b0)
        SUM == (A ^ B ^ CIN)
    );

    // When COUT is 1, SUM equals A&B&CIN (only 3 ones case yields SUM=1).
    check_sum_when_cout1: assert property (
        @(posedge clk) disable iff (1'b0)
        (COUT == 1'b1) |-> (SUM == (A & B & CIN))
    );

    // When COUT is 0, SUM equals A|B|CIN (exactly one 1 yields SUM=1).
    check_sum_when_cout0: assert property (
        @(posedge clk) disable iff (1'b0)
        (COUT == 1'b0) |-> (SUM == (A | B | CIN))
    );

    // All inputs 0 -> outputs 0.
    check_zero_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
        ({A,B,CIN} == 3'b000) |-> (COUT == 1'b0 && SUM == 1'b0)
    );

    // Exactly one input 1 -> SUM=1, COUT=0.
    check_one_hot_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ({A,B,CIN} inside {3'b001,3'b010,3'b100}) |-> (COUT == 1'b0 && SUM == 1'b1)
    );

    // Exactly two inputs 1 -> SUM=0, COUT=1.
    check_two_ones_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ({A,B,CIN} inside {3'b011,3'b101,3'b110}) |-> (COUT == 1'b1 && SUM == 1'b0)
    );

    // All inputs 1 -> outputs 1.
    check_all_ones_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ({A,B,CIN} == 3'b111) |-> (COUT == 1'b1 && SUM == 1'b1)
    );

    // If A equals B, COUT equals that value (majority determined by the pair).
    check_cout_when_A_eq_B: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == B) |-> (COUT == A)
    );

    // If A equals B, SUM equals CIN (A^B cancels).
    check_sum_when_A_eq_B: assert property (
        @(posedge clk) disable iff (1'b0)
        (A == B) |-> (SUM == CIN)
    );
endmodule