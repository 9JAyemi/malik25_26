module and_en(
    input A,
    input B,
    input C1,
    output Y
);

    wire Out;

    and (Out, A, B);

    assign Y = Out & C1;

endmodule