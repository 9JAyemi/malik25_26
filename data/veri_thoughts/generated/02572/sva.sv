module sky130_fd_sc_ls__fa_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic CIN,
    input logic COUT,
    input logic SUM
);
    // COUT implements majority(A,B,CIN)
    check_cout_majority: assert property (
        @(posedge CLK) COUT == ((A & B) | (A & CIN) | (B & CIN))
    );

    // SUM implements A ^ B ^ CIN
    check_sum_xor: assert property (
        @(posedge CLK) SUM == (A ^ B ^ CIN)
    );

    // {COUT,SUM} equals the 2-bit sum of A+B+CIN
    check_add_2bit: assert property (
        @(posedge CLK) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CIN})
    );

    // For inputs 000, outputs are 00
    check_case_all_zero: assert property (
        @(posedge CLK) (!A && !B && !CIN) |-> (!COUT && !SUM)
    );

    // For exactly one input HIGH, outputs are COUT=0, SUM=1
    check_case_exactly_one: assert property (
        @(posedge CLK) ((A ^ B ^ CIN) && !(A && B && CIN)) |-> (!COUT && SUM)
    );

    // For exactly two inputs HIGH, outputs are COUT=1, SUM=0
    check_case_exactly_two: assert property (
        @(posedge CLK) ((A && B && !CIN) || (A && !B && CIN) || (!A && B && CIN)) |-> (COUT && !SUM)
    );

    // For inputs 111, outputs are 11
    check_case_all_ones: assert property (
        @(posedge CLK) (A && B && CIN) |-> (COUT && SUM)
    );

    // If inputs hold their values across a cycle, outputs hold as well
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate)
            (A == $past(A) && B == $past(B) && CIN == $past(CIN)) |-> (SUM == $past(SUM) && COUT == $past(COUT))
    );
endmodule