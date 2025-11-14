module synchronizer (
  input data_in,
  input clk_in,
  input rst,
  output data_out,
  output clk_out
);

parameter n = 3; // number of synchronizer stages

reg [n-1:0] sync_data;
reg [n-1:0] sync_clk;

always @(posedge clk_in or negedge rst) begin
  if (~rst) begin
    sync_data <= {n{1'b0}};
    sync_clk <= {n{1'b0}};
  end
  else begin
    sync_data <= {sync_data[n-2:0], data_in};
    sync_clk <= {sync_clk[n-2:0], clk_in};
  end
end

assign data_out = sync_data[n-1];
assign clk_out = sync_clk[n-1];

endmodule

module synchronizer_reverse (
  input data_in,
  input clk_in,
  input rst,
  output data_out,
  output clk_out
);

parameter n = 3; // number of synchronizer stages

reg [n-1:0] sync_data;
reg [n-1:0] sync_clk;

always @(posedge clk_in or negedge rst) begin
  if (~rst) begin
    sync_data <= {n{1'b0}};
    sync_clk <= {n{1'b0}};
  end
  else begin
    sync_data <= {sync_data[n-2:0], data_in};
    sync_clk <= {sync_clk[n-2:0], clk_in};
  end
end

assign data_out = sync_data[n-1];
assign clk_out = sync_clk[n-1];

endmodule