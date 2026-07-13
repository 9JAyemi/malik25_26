module full_adder (
    input A, B, CARRY_IN,
    output SUM, CARRY_OUT
);

    assign {CARRY_OUT, SUM} = A + B + CARRY_IN;

endmodule

module four_bit_adder(
    input [3:0] A, B,
    output [3:0] OUT,
    output CARRY_OUT,
    input CARRY_IN
);

    wire [3:0] SUM;
    wire CO1, CO2, CO3;
    
    // First full adder
    full_adder FA1 (.A(A[0]), .B(B[0]), .CARRY_IN(CARRY_IN), .SUM(SUM[0]), .CARRY_OUT(CO1));
    
    // Second full adder
    full_adder FA2 (.A(A[1]), .B(B[1]), .CARRY_IN(CO1), .SUM(SUM[1]), .CARRY_OUT(CO2));
    
    // Third full adder
    full_adder FA3 (.A(A[2]), .B(B[2]), .CARRY_IN(CO2), .SUM(SUM[2]), .CARRY_OUT(CO3));
    
    // Fourth full adder
    full_adder FA4 (.A(A[3]), .B(B[3]), .CARRY_IN(CO3), .SUM(SUM[3]), .CARRY_OUT(CARRY_OUT));
    
    // Assign the output
    assign OUT = SUM;
    
endmodule