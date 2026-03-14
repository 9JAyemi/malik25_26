module full_adder_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);
    // SUM must equal A xor B xor CI.
    check_sum_logic: assert property (
        @(posedge CLK) SUM == (A ^ B ^ CI)
    );

    // COUT must equal majority of A,B,CI (carry-out).
    check_cout_logic: assert property (
        @(posedge CLK) COUT == ((A & B) | (B & CI) | (CI & A))
    );

    // {COUT,SUM} equals the 2-bit addition of inputs.
    check_add_result_vector: assert property (
        @(posedge CLK) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // 000 inputs produce 00 outputs.
    truth_000: assert property (
        @(posedge CLK) (A == 1'b0 && B == 1'b0 && CI == 1'b0) |-> (SUM == 1'b0 && COUT == 1'b0)
    );

    // 111 inputs produce 11 outputs.
    truth_111: assert property (
        @(posedge CLK) (A == 1'b1 && B == 1'b1 && CI == 1'b1) |-> (SUM == 1'b1 && COUT == 1'b1)
    );

    // Exactly one input high yields SUM=1 and COUT=0.
    onehot_sum_only: assert property (
        @(posedge CLK) $onehot({A,B,CI}) |-> (SUM == 1'b1 && COUT == 1'b0)
    );

    // Exactly two inputs high yields SUM=0 and COUT=1.
    two_ones_cout_only: assert property (
        @(posedge CLK) ((A & B & ~CI) | (A & CI & ~B) | (B & CI & ~A)) |-> (SUM == 1'b0 && COUT == 1'b1)
    );

    // SUM=1 and COUT=1 implies all three inputs are 1.
    sum_and_cout_imply_three_ones: assert property (
        @(posedge CLK) (SUM == 1'b1 && COUT == 1'b1) |-> (A & B & CI)
    );
endmodule