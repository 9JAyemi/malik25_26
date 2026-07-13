
module top_module (
    input [3:0] DIN,
    input [1:0] SHIFT,
    input [3:0] a,
    input [3:0] b,
    input cin,
    output cout,
    output [3:0] sum,
    output [3:0] DOUT
);

    wire [3:0] shifted_input;
    wire [3:0] adder_input;
    wire [3:0] adder_output;
    
    barrel_shifter barrel_shifter_inst(
        .DIN(DIN),
        .SHIFT(SHIFT),
        .DOUT(shifted_input)
    );
    
    four_bit_adder adder_inst(
        .a(a),
        .b(shifted_input),
        .cin(cin),
        .cout(cout),
        .sum(adder_output)
    );
    
    assign adder_input = b;
    
    assign sum = adder_output + adder_input + cin;
    assign DOUT = adder_output;

endmodule
module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output cout,
    output [3:0] sum
);
    
    assign {cout, sum} = a + b + cin;
    
endmodule
module barrel_shifter (
    input [3:0] DIN,
    input [1:0] SHIFT,
    output [3:0] DOUT
);
    
    assign DOUT = {DIN[SHIFT[1]], DIN[SHIFT[0]], DIN[3], DIN[2]};
    
endmodule