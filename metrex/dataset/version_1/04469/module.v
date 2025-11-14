module gray_code_state_machine #(
  parameter n = 4 // number of bits in the Gray code sequence
)(
  input clk, // clock signal
  input rst, // reset signal
  output [n-1:0] state // Gray code state
);


// define the next state logic here
reg [n-1:0] next_state;
always @(posedge clk, posedge rst) begin
  if (rst) begin
    next_state <= 0;
  end else begin
    next_state <= next_state + 1;
    if (next_state == (1 << n)) begin
      next_state <= 0;
    end
  end
end

// convert binary state to Gray code format
function [n-1:0] binary_to_gray;
  input [n-1:0] binary;
  begin
    binary_to_gray = binary ^ (binary >> 1);
  end
endfunction

// assign Gray code state to output
assign state = binary_to_gray(next_state);

endmodule