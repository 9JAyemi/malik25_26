
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input CLK,
    input RST,
    output reg [3:0] C
);

    wire [3:0] sum;
    wire [3:0] carry;

endmodule

module full_adder (
    input A,
    input B,
    input CIN,
    output COUT,
    output SUM
);
    assign SUM = A ^ B ^ CIN; // XOR gate for sum
    assign COUT = (A & B) | (B & CIN) | (A & CIN); // OR gate for carry
endmodule
