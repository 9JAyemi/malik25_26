module adder16(
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    wire [15:0] carry;
    
    assign carry[0] = cin;
    genvar i;
    generate
        for (i = 1; i < 16; i = i + 1) begin
            full_adder fa(
                .a(a[i]),
                .b(b[i]),
                .cin(carry[i-1]),
                .sum(sum[i]),
                .cout(carry[i])
            );
        end
    endgenerate
    
    assign sum[0] = a[0] ^ b[0] ^ cin;
    assign cout = carry[15];
    
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