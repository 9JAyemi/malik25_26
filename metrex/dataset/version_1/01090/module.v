
module xor_gate (
    input A,
    input B,
    output X,
    input VPWR,
    input VGND
);

    wire not_A;
    wire not_B;
    wire A_and_not_B;
    wire not_A_and_B;

    not (not_A, A);
    not (not_B, B);
    and (A_and_not_B, A, not_B);
    and (not_A_and_B, not_A, B);

    or (X, A_and_not_B, not_A_and_B);

endmodule
