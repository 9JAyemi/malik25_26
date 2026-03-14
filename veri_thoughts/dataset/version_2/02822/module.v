
module multiplexer #(parameter N = 8, M = 2) (
    input [N-1:0] A,
    input [N-1:0] B,
    input [N-1:0] C,
    input [M-1:0] S,
    output [N-1:0] Y
);

// Declare a register to hold the selected input
reg [N-1:0] selected_input;

always @(*) begin
    case (S)
        2'b00: selected_input = A;
        2'b01: selected_input = B;
        2'b10: selected_input = C;
        default: selected_input = 0; // Optional default case
    endcase
end

// Assign the selected input to the output
assign Y = selected_input;

endmodule