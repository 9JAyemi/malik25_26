module top_module (
    input [2:0] sel,
    input [3:0] a0,
    input [3:0] b0,
    input [3:0] a1,
    input [3:0] b1,
    output [3:0] result
);

    // Define the two 4-bit adders
    wire [4:0] sum0, sum1;
    wire cout0, cout1;
    adder4 adder0(.a(a0), .b(b0), .sum(sum0), .cout(cout0));
    adder4 adder1(.a(a1), .b(b1), .sum(sum1), .cout(cout1));

    // Define the bitwise AND of the two least significant bits of all inputs
    wire [1:0] and_out;
    assign and_out = (a0[1:0] & b0[1:0] & a1[1:0] & b1[1:0]);

    // Define the 6-to-1 multiplexer
    wire [4:0] mux_out;
    assign mux_out = (sel == 0) ? {1'b0, sum0} :
                     (sel == 1) ? {1'b0, sum1} :
                     (sel == 2) ? {1'b0, sum0 + sum1} :
                     (sel == 3) ? {1'b0, sum0 - sum1} :
                     (sel == 4) ? {1'b0, sum1 - sum0} :
                     (sel == 5) ? {1'b0, cout0 + cout1} :
                     (sel == 6) ? {1'b0, and_out} :
                                  {1'b0, 4'b1111};

    // Define the output
    assign result = mux_out[3:0];

endmodule

// Define the 4-bit adder module
module adder4 (
    input [3:0] a,
    input [3:0] b,
    output [4:0] sum,
    output cout
);

    assign sum = a + b;
    assign cout = (sum[4] == 1);

endmodule