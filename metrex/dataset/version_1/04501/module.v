module priority_mux (
    input A,
    input B,
    input C,
    input S,
    input P,
    output Y
);

    assign Y = (P) ? C : ((S) ? B : A);

endmodule