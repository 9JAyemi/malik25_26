
module DEMUX #(
  parameter n = 4 // number of output signals
)(
  input in,
  input [n-1:0] control, // binary number to determine which output signal should be set to 1
  output reg [n-1:0] out
);

wire [n-1:0] temp; // temporary register to hold the output values

always @ (in, control) begin
  if (in == 0) begin
    out <= 0;
  end else begin
    case (control)
      0: out <= {1'b1, 1'b0, 1'b0, 1'b0}; // set out1 to 1
      1: out <= {1'b0, 1'b1, 1'b0, 1'b0}; // set out2 to 1
      2: out <= {1'b0, 1'b0, 1'b1, 1'b0}; // set out3 to 1
      3: out <= {1'b0, 1'b0, 1'b0, 1'b1}; // set out4 to 1
      default: out <= 0; // if control is not within 0 to 3, set all output signals to 0
    endcase
  end
end

endmodule