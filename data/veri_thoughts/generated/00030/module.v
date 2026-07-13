
module four_bit_adder (
    A,
    B,
    CI,
    SUM,
    COUT
);

    input [3:0] A;
    input [3:0] B;
    input CI;
    output [3:0] SUM;
    output COUT;

    wire [3:0] a_xor_b;
    wire [3:0] a_xor_b_xor_ci;
    wire [3:0] a_and_b;
    wire [3:0] a_and_b_and_ci;
    wire [3:0] a_or_b;
    wire [3:0] a_or_b_or_ci;
    wire a_xor_b_xor_ci_xor_cout;

    // Implement the adder logic using only the allowed gates and the named wires
    xor xor0 (a_xor_b[0], A[0], B[0]);
    xor xor1 (a_xor_b[1], A[1], B[1]);
    xor xor2 (a_xor_b[2], A[2], B[2]);
    xor xor3 (a_xor_b[3], A[3], B[3]);
    
    xor xor4 (a_xor_b_xor_ci[0], a_xor_b[0], CI);
    xor xor5 (a_xor_b_xor_ci[1], a_xor_b[1], CI);
    xor xor6 (a_xor_b_xor_ci[2], a_xor_b[2], CI);
    xor xor7 (a_xor_b_xor_ci[3], a_xor_b[3], CI);
    
    and and0 (a_and_b[0], A[0], B[0]);
    and and1 (a_and_b[1], A[1], B[1]);
    and and2 (a_and_b[2], A[2], B[2]);
    and and3 (a_and_b[3], A[3], B[3]);
    
    and and4 (a_and_b_and_ci[0], a_and_b[0], CI);
    and and5 (a_and_b_and_ci[1], a_and_b[1], CI);
    and and6 (a_and_b_and_ci[2], a_and_b[2], CI);
    and and7 (a_and_b_and_ci[3], a_and_b[3], CI);
    
    or or0 (a_or_b[0], A[0], B[0]);
    or or1 (a_or_b[1], A[1], B[1]);
    or or2 (a_or_b[2], A[2], B[2]);
    or or3 (a_or_b[3], A[3], B[3]);
    
    or or4 (a_or_b_or_ci[0], a_or_b[0], CI);
    or or5 (a_or_b_or_ci[1], a_or_b[1], CI);
    or or6 (a_or_b_or_ci[2], a_or_b[2], CI);
    or or7 (a_or_b_or_ci[3], a_or_b[3], CI);
    
    xor xor8 (a_xor_b_xor_ci_xor_cout, a_xor_b_xor_ci[3], a_and_b_and_ci[3]);
    
    // Assign the output ports
    assign SUM = a_xor_b_xor_ci;
    assign COUT = a_xor_b_xor_ci_xor_cout;

endmodule
