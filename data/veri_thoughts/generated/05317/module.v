
module nor3 (
    input A,
    input B,
    input C,
    output Y
);

    // Create three inverters
    wire invA, invB, invC;
    not (invA, A);
    not (invB, B);
    not (invC, C);

    // Create a NOR gate with two inputs
    wire norAB;
    nor (norAB, invA, invB);

    // Create a NOR gate with three inputs
    wire norABC;
    nor (norABC, norAB, invC);

    // Assign output to norABC
    assign Y = norABC;

endmodule