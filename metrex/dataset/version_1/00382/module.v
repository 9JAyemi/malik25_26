
module GrayCodeStateMachine #(
  parameter n = 4, // number of input signals
  parameter m = 2 // number of output signals
)(
  input clk,
  input rst,
  input [n-1:0] in,
  output [m-1:0] out
);

// Define internal signals
reg [n-1:0] state_reg;
reg [n-1:0] state_next;
wire [m-1:0] out_logic;

// Gray code encoding
function [n-1:0] gray_encode;
  input [n-1:0] binary;
  begin
    gray_encode = binary ^ (binary >> 1);
  end
endfunction

// State register
always @(posedge clk, posedge rst) begin
  if (rst) begin
    state_reg <= 0;
  end else begin
    state_reg <= state_next;
  end
end

// Next-state logic
always @(*) begin
  case (state_reg)
    // Define state transitions using Gray code
    4'b0000: state_next = gray_encode({in[0], in[1], in[2], in[3]});
    4'b0001: state_next = gray_encode({in[0], in[1], in[2], ~in[3]});
    4'b0011: state_next = gray_encode({in[0], in[1], ~in[2], in[3]});
    4'b0010: state_next = gray_encode({in[0], in[1], ~in[2], ~in[3]});
    4'b0110: state_next = gray_encode({in[0], ~in[1], in[2], in[3]});
    4'b0111: state_next = gray_encode({in[0], ~in[1], in[2], ~in[3]});
    4'b0101: state_next = gray_encode({in[0], ~in[1], ~in[2], in[3]});
    4'b0100: state_next = gray_encode({in[0], ~in[1], ~in[2], ~in[3]});
    4'b1100: state_next = gray_encode({~in[0], in[1], in[2], in[3]});
    4'b1101: state_next = gray_encode({~in[0], in[1], in[2], ~in[3]});
    4'b1111: state_next = gray_encode({~in[0], in[1], ~in[2], in[3]});
    4'b1110: state_next = gray_encode({~in[0], in[1], ~in[2], ~in[3]});
    4'b1010: state_next = gray_encode({~in[0], ~in[1], in[2], in[3]});
    4'b1011: state_next = gray_encode({~in[0], ~in[1], in[2], ~in[3]});
    4'b1001: state_next = gray_encode({~in[0], ~in[1], ~in[2], in[3]});
    4'b1000: state_next = gray_encode({~in[0], ~in[1], ~in[2], ~in[3]});
    default: state_next = 0;
  endcase
end

// Output logic
assign out_logic = (state_reg == {~in[0], ~in[1], ~in[2], ~in[3]}) ? {1'b0, 1'b0} :
                  (state_reg == {~in[0], ~in[1], ~in[2], in[3]}) ? {1'b0, 1'b1} :
                  (state_reg == {~in[0], ~in[1], in[2], ~in[3]}) ? {1'b1, 1'b0} :
                  (state_reg == {~in[0], ~in[1], in[2], in[3]}) ? {1'b1, 1'b1} :
                  (state_reg == {~in[0], in[1], ~in[2], ~in[3]}) ? {1'b0, 1'b1} :
                  (state_reg == {~in[0], in[1], ~in[2], in[3]}) ? {1'b0, 1'b0} :
                  (state_reg == {~in[0], in[1], in[2], ~in[3]}) ? {1'b1, 1'b1} :
                  (state_reg == {~in[0], in[1], in[2], in[3]}) ? {1'b1, 1'b0} :
                  (state_reg == {in[0], ~in[1], ~in[2], ~in[3]}) ? {1'b1, 1'b1} :
                  (state_reg == {in[0], ~in[1], ~in[2], in[3]}) ? {1'b1, 1'b0} :
                  (state_reg == {in[0], ~in[1], in[2], ~in[3]}) ? {1'b0, 1'b1} :
                  (state_reg == {in[0], ~in[1], in[2], in[3]}) ? {1'b0, 1'b0} :
                  (state_reg == {in[0], in[1], ~in[2], ~in[3]}) ? {1'b1, 1'b0} :
                  (state_reg == {in[0], in[1], ~in[2], in[3]}) ? {1'b1, 1'b1} :
                  (state_reg == {in[0], in[1], in[2], ~in[3]}) ? {1'b0, 1'b0} :
                  (state_reg == {in[0], in[1], in[2], in[3]}) ? {1'b0, 1'b1} : 2'bxx;

// Assign output signals
assign out = out_logic;

endmodule
