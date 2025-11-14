module top_module( 
    input a, b, c, // Three bits to be added
    input select, // Select input to choose between two half adder modules
    output [2:0] sum // 3-bit output from the active module
);

    wire ha1_cout, ha1_sum, ha2_cout, ha2_sum;
    wire [1:0] ha_sel;

    // Control logic module to select between two half adder modules
    assign ha_sel = select ? 2'b10 : 2'b01;

    // First half adder module to add the first two bits
    half_adder ha1(
        .a(a),
        .b(b),
        .cout(ha1_cout),
        .sum(ha1_sum)
    );

    // Second half adder module to add the result with the third input bit
    half_adder ha2(
        .a(ha_sel[0] ? ha1_sum : ha1_cout),
        .b(c),
        .cout(ha2_cout),
        .sum(ha2_sum)
    );

    // Final sum module to output the sum of the three bits
    final_sum fs(
        .cin(ha_sel[1] ? ha2_cout : ha1_cout),
        .sum(ha2_sum),
        .out(sum)
    );

endmodule

module half_adder(
    input a, b,
    output cout, sum // Carry-out and sum outputs
);

    assign {cout, sum} = a + b;

endmodule

module final_sum(
    input cin, sum,
    output [2:0] out // 3-bit output
);

    assign out = {cin, sum};

endmodule