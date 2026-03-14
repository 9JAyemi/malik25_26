
module and_or_not (
    input A,
    input B,
    input C,
    output Y
);

wire and_result, not_result;

assign and_result = A & B;
assign not_result = !C;
assign Y = and_result | not_result;

endmodule