
module or3_circuit(
    input wire A,
    input wire B,
    input wire C,
    output wire X
);

    wire temp;
    or orlando(temp, A, B);
    or _4_(X, temp, C);

endmodule