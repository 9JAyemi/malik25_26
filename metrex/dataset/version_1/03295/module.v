

module ad_rst (

  preset,
  clk,
  rst);

  input           preset;
  input           clk;
  output          rst;

  reg             ad_rst_sync_m1 = 'd0 ;
  reg             ad_rst_sync = 'd0 ;
  reg             rst = 'd0;

  always @(posedge clk) begin
    ad_rst_sync_m1 <= preset;
    ad_rst_sync <= ad_rst_sync_m1;
    rst <= ad_rst_sync;
  end

endmodule

