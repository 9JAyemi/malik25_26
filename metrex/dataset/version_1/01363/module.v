module mux_4to1 (
    input A,
    input B,
    input C,
    input D,
    input S0,
    input S1,
    output Y
);

    wire sel1, sel2;

    // First level of selection
    assign sel1 = (S1 == 0) ? S0 : ~S0;

    // Second level of selection
    assign sel2 = (S1 == 0) ? A : B;
    assign Y = (sel1 & sel2) | (~sel1 & ((S1 == 0) ? C : D));

endmodule