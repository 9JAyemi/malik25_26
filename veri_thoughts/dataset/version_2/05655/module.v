module priority_encoder (
    input [3:0] I,
    output reg [1:0] encoded
);

always @* begin
    case (I)
        4'b0001: encoded = 2'b00;
        4'b0010: encoded = 2'b01;
        4'b0100: encoded = 2'b10;
        4'b1000: encoded = 2'b11;
        default: encoded = 2'b00;
    endcase
end

endmodule

module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output reg [3:0] result
);

always @* begin
    if (SUB) begin
        result = A - B;
    end else begin
        result = A + B;
    end
end

endmodule

module functional_module (
    input [1:0] encoded,
    input [3:0] adder_subtractor_output,
    output reg [3:0] result
);

always @* begin
    case (encoded)
        2'b00: result = adder_subtractor_output;
        2'b01: result = adder_subtractor_output + 1;
        2'b10: result = adder_subtractor_output + 2;
        2'b11: result = adder_subtractor_output + 3;
        default: result = adder_subtractor_output;
    endcase
end

endmodule

module top_module (
    input [3:0] I,
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output [3:0] result
);

wire [1:0] encoded;
wire [3:0] adder_subtractor_output;

priority_encoder pe (
    .I(I),
    .encoded(encoded)
);

adder_subtractor as (
    .A(A),
    .B(B),
    .SUB(SUB),
    .result(adder_subtractor_output)
);

functional_module fm (
    .encoded(encoded),
    .adder_subtractor_output(adder_subtractor_output),
    .result(result)
);

endmodule