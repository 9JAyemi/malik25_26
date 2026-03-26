
module square_wave_generator (
    input clk,
    input reset,
    output reg square_wave
);

reg [31:0] counter;

always @(posedge clk, posedge reset) begin
    if (reset) begin
        square_wave <= 1'b0;
        counter <= 32'd0;
    end else begin
        if (counter == 32'd49999999) begin
            counter <= 32'd0;
            square_wave <= ~square_wave;
        end else begin
            counter <= counter + 1;
        end
    end
end

endmodule

module adder (
    input [15:0] A,
    input [15:0] B,
    input Cin,
    output [15:0] S,
    output Cout
);

assign {Cout, S} = A + B + Cin;

endmodule

module final_module (
    input clk,
    input reset,
    input [15:0] A,
    input [15:0] B,
    input Cin,
    output [15:0] final_output
);

wire square_wave;
wire [15:0] adder_output;
wire [15:0] subtractor_output;

square_wave_generator square_wave_gen (
    .clk(clk),
    .reset(reset),
    .square_wave(square_wave)
);

adder adder_inst (
    .A(A),
    .B(B),
    .Cin(Cin),
    .S(adder_output),
    .Cout()
);

assign subtractor_output = A - B;

assign final_output = square_wave ? adder_output + subtractor_output : adder_output - subtractor_output;

endmodule

module top_module (
    input clk,
    input reset,
    input [15:0] A,
    input [15:0] B,
    input Cin,
    output [15:0] final_output
);

final_module final_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .Cin(Cin),
    .final_output(final_output)
);

endmodule
