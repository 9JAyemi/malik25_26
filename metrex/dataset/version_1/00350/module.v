
module barrel_shifter (
  input [bus_size-1:0] input_bus,
  input [shift_amount_size-1:0] shift_amount,
  input shift_direction,
  output [bus_size-1:0] output_bus
);

parameter bus_size = 8; // size of input and output bus
parameter shift_amount_size = 3; // number of bits needed to represent shift_amount
parameter width = bus_size - shift_amount_size; // width of the shift register

// Declare temporary register to store shifted bus
reg [bus_size-1:0] shifted_bus; 

// RTL code for barrel shifter
always @(*) begin
  if (shift_direction) begin // left shift
    shifted_bus = input_bus << shift_amount;
  end else begin // right shift
    shifted_bus = input_bus >> shift_amount;
  end
end

// Assign output bus to the shifted bus
assign output_bus = shifted_bus;

endmodule
