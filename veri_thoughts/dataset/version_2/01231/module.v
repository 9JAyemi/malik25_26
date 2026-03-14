module top_module (
    input [3:0] a, // 4-bit input A
    input [3:0] b, // 4-bit input B
    input select, // Select input to choose between adder and multiplexer
    output [3:0] out // 4-bit output
);

    wire [3:0] add_out; // Output of the 4-bit adder
    wire carry_out; // Carry-out bit of the 4-bit adder

    // Instantiate the 4-bit adder module
    adder_module adder_inst (
        .a(a),
        .b(b),
        .sum(add_out),
        .carry_out(carry_out)
    );

    // Instantiate the 2-to-1 multiplexer module
    mux2to1_module mux_inst (
        .a(a),
        .b(add_out),
        .select(select),
        .out(out)
    );

endmodule

// 4-bit adder module
module adder_module (
    input [3:0] a, // 4-bit input A
    input [3:0] b, // 4-bit input B
    output [3:0] sum, // 4-bit sum output
    output carry_out // Carry-out bit output
);

    wire [3:0] carry; // Carry bits for each full adder

    // Full adder instances
    full_adder fa0 (.a(a[0]), .b(b[0]), .carry_in(1'b0), .sum(sum[0]), .carry_out(carry[0]));
    full_adder fa1 (.a(a[1]), .b(b[1]), .carry_in(carry[0]), .sum(sum[1]), .carry_out(carry[1]));
    full_adder fa2 (.a(a[2]), .b(b[2]), .carry_in(carry[1]), .sum(sum[2]), .carry_out(carry[2]));
    full_adder fa3 (.a(a[3]), .b(b[3]), .carry_in(carry[2]), .sum(sum[3]), .carry_out(carry_out));

endmodule

// Full adder module
module full_adder (
    input a, // Input A
    input b, // Input B
    input carry_in, // Carry-in bit
    output sum, // Sum output
    output carry_out // Carry-out bit
);

    assign {carry_out, sum} = a + b + carry_in;

endmodule

// 2-to-1 multiplexer module
module mux2to1_module (
    input [3:0] a, // 4-bit input A
    input [3:0] b, // 4-bit input B
    input select, // Select input
    output [3:0] out // 4-bit output
);

    assign out = select ? b : a;

endmodule