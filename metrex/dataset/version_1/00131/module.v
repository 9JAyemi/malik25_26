
module carry_select_adder #(
    parameter WIDTH = 100
) (
    input [WIDTH-1:0] a, b,
    input cin,
    output [WIDTH-1:0] sum,
    output cout
);
    wire [WIDTH-1:0] sum0, sum1;
    wire cout0, cout1;

    adder adder0(
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum0),
        .cout(cout0)
    );

    adder adder1(
        .a(a),
        .b(b),
        .cin(1'b1),
        .sum(sum1),
        .cout(cout1)
    );

    assign sum = cin ? sum1 : sum0;
    assign cout = cin ? cout1 : cout0;
endmodule
module adder #(
    parameter WIDTH = 100
) (
    input [WIDTH-1:0] a, b,
    input cin,
    output [WIDTH-1:0] sum,
    output cout
);
    assign {cout, sum} = a + b + cin;
endmodule
module barrel_shifter #(
    parameter WIDTH = 100
) (
    input [WIDTH-1:0] in,
    input load,
    input [1:0] ena,
    output reg [WIDTH-1:0] out
);
    always @(*) begin
        if (load) begin
            out <= in;
        end else begin
            case (ena)
                2'b00: out <= in;
                2'b01: out <= {in[WIDTH-2:0], in[WIDTH-1]};
                2'b10: out <= {in[WIDTH-3:0], in[WIDTH-2:WIDTH-1]};
                2'b11: out <= {in[WIDTH-4:0], in[WIDTH-3:WIDTH-1]};
            endcase
        end
    end
endmodule
module top_module (
    input [99:0] a, b, // 100-bit inputs for the adder
    input cin, // Carry-in for the adder
    input load, // Load input for the rotator
    input [1:0] ena, // Enable input for the rotator
    output [99:0] sum, // 100-bit sum from the adder
    output [99:0] q // Rotated output from the rotator
);

    // Instantiate the adder and rotator modules
    carry_select_adder adder_inst(
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum)
    );

    barrel_shifter rotator_inst(
        .in(sum),
        .load(load),
        .ena(ena),
        .out(q)
    );
endmodule