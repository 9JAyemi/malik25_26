

module ad_rst (

  input                   rst_async,
  input                   clk,
  output                  rstn,
  output  reg             rst);

  reg             rst_async_d1 = 1'd1;
  reg             rst_async_d2 = 1'd1;
  reg             rst_sync = 1'd1;
  reg             rst_sync_d = 1'd1;

  always @(posedge clk or posedge rst_async) begin
    if (rst_async) begin
      rst_async_d1 <= 1'b1;
      rst_async_d2 <= 1'b1;
      rst_sync <= 1'b1;
    end else begin
      rst_async_d1 <= 1'b0;
      rst_async_d2 <= rst_async_d1;
      rst_sync <= rst_async_d2;
    end
  end

  always @(posedge clk) begin
    rst_sync_d <= rst_sync;
    rst <= rst_sync_d;
  end

  assign rstn = ~rst;

endmodule

