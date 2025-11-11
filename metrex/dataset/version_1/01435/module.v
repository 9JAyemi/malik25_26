
module four_bit_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    input reset,
    output [3:0] Sum,
    output Cout
);

    wire [3:0] xor1_out;
    wire [3:0] xor2_out;
    wire [3:0] and1_out;
    wire [3:0] and2_out;
    wire [3:0] and3_out;
    wire [3:0] or1_out;
    wire [3:0] or2_out;
    wire [3:0] or3_out;
    wire [3:0] or4_out;
    wire [3:0] sum_out;
    wire [3:0] carry_out;

    assign xor1_out = A ^ B;
    assign xor2_out = xor1_out ^ Cin;
    assign and1_out = A & B;
    assign and2_out = A & Cin;
    assign and3_out = B & Cin;
    assign or1_out = and1_out | and2_out;
    assign or2_out = and1_out | and3_out;
    assign or3_out = and2_out | and3_out;
    assign or4_out = or1_out | or2_out | or3_out;
    assign sum_out = xor2_out;
    assign carry_out = or4_out;

    assign Cout = carry_out[3];

    reg [3:0] Sum;

    always @ (posedge reset, posedge Cin) begin
        if (reset) begin
            Sum <= 0;
        end else begin
            Sum <= sum_out;
        end
    end

endmodule