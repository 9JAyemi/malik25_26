module full_adder(
    input a,
    input b,
    input cin,  
    output sum,
    output carry
);
    // Intermediate wires
    wire w1, w2, w3;

    assign w1 = a ^ b;      // XOR for sum calculation
    assign w2 = a & b;      // AND for direct carry
    assign w3 = w1 & cin;   // AND for carry from lower bits

    assign sum = w1 ^ cin;  // Final sum with carry-in
    assign carry = w2 | w3; // Carry is the OR of direct carry and propagated carry
endmodule
