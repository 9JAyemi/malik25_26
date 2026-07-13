module my_and_gate (
    input A,
    input B,
    output X
);

    wire AB;
    wire not_AB;

    and (AB, A, B);

    not (not_AB, AB);

    and (X, not_AB, 1'b1);

endmodule