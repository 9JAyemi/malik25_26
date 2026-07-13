
module my_or2 (
    input A,
    input B,
    output X,
    output PG
);

    wire or_out;

    assign or_out = A | B;

    assign X = or_out;
    assign PG = 1;

endmodule