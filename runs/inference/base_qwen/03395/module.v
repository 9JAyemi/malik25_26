module AND3 (
    input A,
    input B,
    input C,
    output Z
);

// RTL using continuous assignment
assign Z = A & B & C;

endmodule
