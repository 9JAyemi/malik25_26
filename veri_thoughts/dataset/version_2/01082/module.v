
module add_sub_pipeline
(
    input wire [31:0] a,
    input wire [31:0] b,
    input wire        sub,
    output wire [31:0] sum
);

    wire [15:0] a_lsb  ;
    wire [15:0] b_lsb  ;
    wire [15:0] a_msb  ;
    wire [15:0] b_msb  ;
    wire [15:0] sum_lsb;
    wire [15:0] sum_msb;
    wire        cin_msb;
    wire        cin_lsb;

    assign a_lsb  = a[15:0];
    assign b_lsb  = b[15:0];
    assign a_msb  = a[31:16];
    assign b_msb  = b[31:16];

    assign cin_lsb = sub;
    assign cin_msb = sub;

    adder16 adder_lsb(.a(a_lsb), .b(b_lsb), .cin(cin_lsb), .sum(sum_lsb));
    adder16 adder_msb(.a(a_msb), .b(b_msb), .cin(cin_msb), .sum(sum_msb));

    assign sum = {sum_msb, sum_lsb};

endmodule
module adder16
(
    input wire [15:0] a,
    input wire [15:0] b,
    input wire        cin,
    output wire [15:0] sum
);

    wire [15:0] carry;

    assign sum = a + b + cin;
    assign carry = (a[15] & b[15]) | (a[15] & cin) | (b[15] & cin);

endmodule
module twos_complement
(
    input wire  in,
    output wire out
);

    assign out = ~in + 1;

endmodule