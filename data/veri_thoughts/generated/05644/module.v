
module ripple_carry_adder(
    input [7:0] A,
    input [7:0] B,
    input cin,
    output [7:0] sum,
    output cout
    );

    wire [8:0] adder; // 9 bits to store the sum and the carry out

    // Ripple carry adder
    genvar i;
    generate
        for(i=0; i<8; i=i+1) begin
            full_adder fa(
                .a(A[i]),
                .b(B[i]),
                .cin(adder[i]),
                .sum(sum[i]),
                .cout(adder[i+1])
                );
        end
    endgenerate

    assign cout = adder[8];
    assign adder[0] = cin; // Initializing the first carry-in to the input carry-in
    
endmodule
module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
    );

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);
    
endmodule