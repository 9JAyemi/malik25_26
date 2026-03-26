
module full_adder_csa(
    input a, b, cin,
    output cout, sum
);

wire c1, c2, s1, s2;

// First ripple carry adder
ripple_adder RA1(.a(a), .b(b), .cin(cin), .cout(c1), .sum(s1));

// Second ripple carry adder
ripple_adder RA2(.a(a), .b(b), .cin(c1), .cout(c2), .sum(s2));

// 2-to-1 multiplexers
mux2to1 M1(.a(s1), .b(s2), .sel(c1), .out(sum));
mux2to1 M2(.a(c1), .b(c2), .sel(c1), .out(cout));

endmodule
module ripple_adder(
    input a, b, cin,
    output cout, sum
);

wire c1;

// First full adder
full_adder FA1(.a(a), .b(b), .cin(cin), .cout(c1), .sum(sum));

// Second full adder
full_adder FA2(.a(a), .b(b), .cin(c1), .cout(cout), .sum());

endmodule
module full_adder(
    input a, b, cin,
    output cout, sum
);

assign {cout, sum} = a + b + cin;

endmodule
module mux2to1(
    input a, b, sel,
    output out
);

assign out = sel ? b : a;

endmodule