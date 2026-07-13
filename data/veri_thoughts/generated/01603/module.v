
module byte_reorder(
    input [31:0] in,
    input clk,  // Added clock signal as input port
    output [31:0] out
);

wire [7:0] byte0, byte1, byte2, byte3;

// Shift registers to store each byte of the input
reg [7:0] shift_reg0;
reg [7:0] shift_reg1;
reg [7:0] shift_reg2;
reg [7:0] shift_reg3;

// Multiplexers to select the correct byte order
assign byte0 = (in >> 24) & 8'hFF;
assign byte1 = (in >> 16) & 8'hFF;
assign byte2 = (in >> 8) & 8'hFF;
assign byte3 = in & 8'hFF;

// Shift register to reverse byte order
always @ (posedge clk) begin
    shift_reg0 <= byte3;
    shift_reg1 <= byte2;
    shift_reg2 <= byte1;
    shift_reg3 <= byte0;
end

// Multiplexers to select the correct byte order
assign out = {shift_reg0, shift_reg1, shift_reg2, shift_reg3};

endmodule