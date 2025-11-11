module priority_encoder (
    input [3:0] A, B, C, D, // Four 4-bit binary values to be encoded
    input S1, S0, // Select inputs to determine which input to encode
    output reg [1:0] Q // 2-bit output of the priority encoder module
);

always @(*) begin
    if (S1 == 0 && S0 == 0) begin
        if (A > B && A > C && A > D) Q = 0;
        else if (B > C && B > D) Q = 1;
        else if (C > D) Q = 2;
        else Q = 3;
    end
    else if (S1 == 0 && S0 == 1) begin
        if (B > A && B > C && B > D) Q = 0;
        else if (A > C && A > D) Q = 1;
        else if (C > D) Q = 2;
        else Q = 3;
    end
    else if (S1 == 1 && S0 == 0) begin
        if (C > A && C > B && C > D) Q = 0;
        else if (A > B && A > D) Q = 1;
        else if (B > D) Q = 2;
        else Q = 3;
    end
    else if (S1 == 1 && S0 == 1) begin
        if (D > A && D > B && D > C) Q = 0;
        else if (A > B && A > C) Q = 1;
        else if (B > C) Q = 2;
        else Q = 3;
    end
end

endmodule

module adder_subtractor (
    input [3:0] A, B, // Two 4-bit binary values to be added or subtracted
    input Cn, // Carry-in input for the adder
    input Sub, // Subtraction mode select input
    output reg [3:0] S, // 4-bit output of the adder/subtractor module
    output reg Cout // Carry-out output of the adder
);

always @(*) begin
    if (Sub == 1) begin
        S = A - B;
        Cout = ~(A < B);
    end
    else begin
        S = A + B + Cn;
        Cout = (S > 15);
    end
end

endmodule

module top_module (
    input [3:0] A, B, C, D, // Four 4-bit binary values to be added or subtracted
    input S1, S0, // Select inputs to determine which input to encode
    output reg [1:0] encoded_input // 2-bit encoded input for adder_subtractor
);

wire [1:0] pe_output;
priority_encoder pe (
    .A(A),
    .B(B),
    .C(C),
    .D(D),
    .S1(S1),
    .S0(S0),
    .Q(pe_output)
);

always @* begin
    encoded_input = (pe_output == 2'b10 || pe_output == 2'b11) ? 1'b1 : 1'b0;
end

endmodule