module ASYNC_TO_SYNC (
  input in,
  input clk,
  input rst,
  output reg out
);

parameter n = 3; // number of synchronizer stages

reg [n-1:0] sync_reg; // register chain for synchronizer

always @(posedge clk or posedge rst) begin
  if (rst) begin
    sync_reg <= {n{1'b0}}; // reset register chain
    out <= 1'b0; // reset output signal
  end else begin
    sync_reg <= {sync_reg[n-2:0], in}; // shift input signal through register chain
    out <= sync_reg[n-1]; // output final synchronized signal
  end
end

endmodule

module SYNC_TO_ASYNC (
  input clk,
  input rst,
  input in,
  output reg out
);

parameter n = 4; // number of synchronizer stages

reg [n-1:0] sync_reg; // register chain for synchronizer

always @(posedge clk or posedge rst) begin
  if (rst) begin
    sync_reg <= {n{1'b0}}; // reset register chain
    out <= 1'b0; // reset output signal
  end else begin
    sync_reg <= {sync_reg[n-2:0], in}; // shift input signal through register chain
    out <= sync_reg[n-1]; // output final synchronized signal
  end
end

endmodule