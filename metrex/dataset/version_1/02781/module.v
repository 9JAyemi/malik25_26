
module top_module (
    input clk,
    input [11:0] in,
    output [7:0] out
);

    // Split the 12-bit input into lower, middle, and upper bytes
    wire [3:0] lower = in[3:0];
    wire [3:0] middle = in[7:4];
    wire [3:0] upper = in[11:8];

    // Create a 3-bit shift register using master-slave flip-flops
    reg [2:0] shift_reg;
    always @(posedge clk) begin
        shift_reg <= {shift_reg[1:0], lower};
    end

    // Perform a left rotation on the lower byte using the shift register
    wire [3:0] rotated_lower = {shift_reg[2], shift_reg[1], shift_reg[0]};

    // Combine the rotated lower byte, middle byte, and upper byte using a barrel shifter
    wire [11:0] shifted_in = {rotated_lower, middle, upper};
    wire [11:0] and_out;

    // Perform a bitwise AND operation between the shifted input and the original input
    assign and_out = shifted_in & in;

    // Output the result of the AND operation
    assign out = and_out[7:0];

endmodule
module barrel_shifter (
    input [11:0] in,
    input [1:0] shift,
    output [11:0] out
);

    assign out = (shift[1]) ? ({in[7:0], in[11:8], in[3:0]}) :
                             ({in[3:0], in[7:4], in[11:8], in[10:4] >> shift[0]});

endmodule
module and_gate (
    input [11:0] in1,
    input [11:0] in2,
    output [11:0] out
);

    assign out = in1 & in2;

endmodule