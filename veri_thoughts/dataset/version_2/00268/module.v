
module add_sub_4bit(
    input [3:0] A,
    input [3:0] B,
    input mode,
    output reg [3:0] O,
    output reg COUT
);

always @(*) begin
    if (mode == 0) begin // Addition
        {COUT, O} = A + B;
    end
    else begin // Subtraction
        {COUT, O} = A - B;
    end
end

endmodule