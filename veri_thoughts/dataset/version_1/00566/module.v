module OAI21X1(
    input A,    // OR input 1
    input B,    // OR input 2
    input C,    // AND input
    output Y    // Output
);

    // Implement the OAI21 logic: Y = ~(A | B) & C
    assign Y = ~((A | B) & C);

endmodule
