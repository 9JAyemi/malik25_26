
module full_adder(
    input a, b, cin,
    output cout, sum );

    wire w1, w2, w3;

    // First half adder
    half_adder HA1(.a(a), .b(b), .sum(w1), .cout(w2));

    // Second half adder
    half_adder HA2(.a(w1), .b(cin), .sum(sum), .cout(w3));

    // Multiplexer to select carry-out
    assign cout = w2 | w3;

endmodule
module half_adder(
    input a, b,
    output sum, cout );

    assign sum = a ^ b;
    assign cout = a & b;

endmodule