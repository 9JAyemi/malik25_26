module two_bit_comparator_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [1:0] C
);
    // C never encodes 2'b11.
    check_c_never_11: assert property (
        @(posedge CLK) C != 2'b11
    );

    // If A == B then C == 2'b00.
    check_eq_implies_c00: assert property (
        @(posedge CLK) (A == B) |-> (C == 2'b00)
    );

    // If C == 2'b00 then A == B.
    check_c00_implies_eq: assert property (
        @(posedge CLK) (C == 2'b00) |-> (A == B)
    );

    // If A > B then C == 2'b01.
    check_gt_implies_c01: assert property (
        @(posedge CLK) (A > B) |-> (C == 2'b01)
    );

    // If C == 2'b01 then A > B.
    check_c01_implies_gt: assert property (
        @(posedge CLK) (C == 2'b01) |-> (A > B)
    );

    // If A < B then C == 2'b10.
    check_lt_implies_c10: assert property (
        @(posedge CLK) (A < B) |-> (C == 2'b10)
    );

    // If C == 2'b10 then A < B.
    check_c10_implies_lt: assert property (
        @(posedge CLK) (C == 2'b10) |-> (A < B)
    );

    // Output remains stable if inputs remain stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(C)
    );
endmodule