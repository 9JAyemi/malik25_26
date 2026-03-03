// SVA for ripple_carry_adder
// Bind into DUT to access internal carry chain
checker rca_checker (
    input logic [3:0] A, B, SUM,
    input logic       CIN, COUT,
    input logic [3:0] carry
);
    // Functional equivalence of the whole adder
    property p_total_correct;
        @(A or B or CIN)
        !$isunknown({A,B,CIN}) |-> ##0 {COUT,SUM} == (A + B + CIN);
    endproperty
    assert property (p_total_correct);

    // X-propagation: clean outputs when inputs are clean
    property p_no_x_out;
        @(A or B or CIN)
        !$isunknown({A,B,CIN}) |-> ##0 !$isunknown({SUM,COUT,carry[2:0]});
    endproperty
    assert property (p_no_x_out);

    // Bit-slice correctness and carry chain linking
    // Stage 0
    property p_s0;
        @(A or B or CIN)
        !$isunknown({A[0],B[0],CIN}) |-> ##0
            (SUM[0] == (A[0]^B[0]^CIN)) &&
            (carry[0] == ((A[0]&B[0]) | (B[0]&CIN) | (CIN&A[0])));
    endproperty
    assert property (p_s0);

    // Stage 1
    property p_s1;
        @(A or B or CIN or carry[0])
        !$isunknown({A[1],B[1],carry[0]}) |-> ##0
            (SUM[1] == (A[1]^B[1]^carry[0])) &&
            (carry[1] == ((A[1]&B[1]) | (B[1]&carry[0]) | (carry[0]&A[1])));
    endproperty
    assert property (p_s1);

    // Stage 2
    property p_s2;
        @(A or B or CIN or carry[1])
        !$isunknown({A[2],B[2],carry[1]}) |-> ##0
            (SUM[2] == (A[2]^B[2]^carry[1])) &&
            (carry[2] == ((A[2]&B[2]) | (B[2]&carry[1]) | (carry[1]&A[2])));
    endproperty
    assert property (p_s2);

    // Stage 3 (final)
    property p_s3;
        @(A or B or CIN or carry[2])
        !$isunknown({A[3],B[3],carry[2]}) |-> ##0
            (SUM[3] == (A[3]^B[3]^carry[2])) &&
            (COUT   == ((A[3]&B[3]) | (B[3]&carry[2]) | (carry[2]&A[3])));
    endproperty
    assert property (p_s3);

    // Concise functional coverage
    // Zero add, no carry
    cover property (@(A or B or CIN) ##0 (A==4'h0 && B==4'h0 && CIN==0 && SUM==4'h0 && COUT==0));
    // Max add with carry-out
    cover property (@(A or B or CIN) ##0 (A==4'hF && B==4'hF && CIN==1 && SUM==4'hF && COUT==1));
    // Full propagate chain (all P=1) with carry-in=1 causes carry-out
    cover property (@(A or B or CIN) ##0 ((A^B)==4'hF && CIN==1 && COUT==1));
    // Observe carries through the chain at least once
    cover property (@(A or B or CIN) ##0 (carry[0]));
    cover property (@(A or B or CIN) ##0 (carry[1]));
    cover property (@(A or B or CIN) ##0 (carry[2]));
    cover property (@(A or B or CIN) ##0 (COUT));
endchecker

bind ripple_carry_adder rca_checker rca_chk (
    .A(A), .B(B), .SUM(SUM), .CIN(CIN), .COUT(COUT), .carry(carry)
);