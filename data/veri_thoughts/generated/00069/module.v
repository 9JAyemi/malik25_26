
module adder(
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum,
    output carry
);

    assign {carry, sum} = a + b;

    // Buffers to drive the output ports
    reg [3:0] sum_buf;
    reg carry_buf;

    always @* begin
        sum_buf = sum;
        carry_buf = carry;
    end

endmodule