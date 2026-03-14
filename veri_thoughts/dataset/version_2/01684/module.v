module mux_2to1_with_control(
    input A,
    input B,
    input Sel,
    output Out
);

    wire Sel_not;
    assign Sel_not = ~Sel;

    wire B_not;
    assign B_not = ~B;

    wire Sel_and_B;
    assign Sel_and_B = Sel & B;

    wire Sel_and_B_not;
    assign Sel_and_B_not = Sel & B_not;

    wire A_select;
    assign A_select = Sel_not & A;

    wire B_select;
    assign B_select = Sel_and_B_not | Sel_and_B;

    assign Out = A_select | B_select;

endmodule