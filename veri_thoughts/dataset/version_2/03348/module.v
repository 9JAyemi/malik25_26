module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    input clk,
    output [3:0] S,
    output Cout
);

    reg [3:0] S;
    reg Cout;

    always @(posedge clk) begin
        S <= A + B + Cin;
        Cout <= (A + B + Cin > 15) ? 1 : 0;
    end

endmodule