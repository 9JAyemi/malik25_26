module reset_sync (
  input rst,
  input clk,
  output reg rst_sync
);

  reg [1:0] rst_sync_reg;

  always @(posedge clk) begin
    rst_sync_reg <= {rst_sync_reg[0], rst};
  end

  always @(*) begin
    rst_sync = ~rst_sync_reg[1];
  end

endmodule