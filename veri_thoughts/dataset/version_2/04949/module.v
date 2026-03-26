
module ff32_en_SIZE13_shift (
  input [12:0] D,
  output [12:0] Q,
  input en,
  input clk,
  input rst,
  input shift
);
  wire [12:0] Q_reg;
  wire [12:0] Q_shifted;
  wire [12:0] D_shifted;

  // Original 13-bit register module
  reg [12:0] original_Q_reg;
  wire [12:0] original_D;
  always @(posedge clk or posedge rst) begin
    if (rst) begin
      original_Q_reg <= 13'd0;
    end else begin
      if (en) begin
        original_Q_reg <= D;
      end
    end
  end

  // Shift the data input to the left
  assign D_shifted = shift ? {D[11:0], 1'b0} : D;

  // Shift the register output to the left
  assign Q_shifted = {original_Q_reg[11:0], 1'b0};

  // Connect the output to the shifted register output if shift is high
  // Otherwise, connect the output to the original register output
  assign Q = shift ? Q_shifted : original_Q_reg;

  // Connect the data input to the shifted data input if shift is high
  // Otherwise, connect the data input to the original data input
  assign original_D = D_shifted;
endmodule