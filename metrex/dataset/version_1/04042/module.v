module CDR (
  input data_in,
  input clk_ref,
  output clk_out,
  output data_out
);

  // Internal signals
  reg data_in_delayed;
  reg [1:0] data_in_edge;
  reg clk_out_delayed;
  reg data_out_delayed;
  
  // Delayed data input
  always @(posedge clk_ref) begin
    data_in_delayed <= data_in;
  end
  
  // Detect data input edges
  always @(posedge clk_ref) begin
    data_in_edge <= {data_in_delayed, data_in} - {data_in, data_in_delayed};
  end
  
  // Generate recovered clock
  always @(posedge clk_ref) begin
    if (data_in_edge == 2'b01 || data_in_edge == 2'b10) begin
      clk_out_delayed <= ~clk_out_delayed;
    end
  end
  
  // Generate recovered data
  always @(posedge clk_out_delayed) begin
    data_out_delayed <= data_in_delayed;
  end
  
  // Output signals
  assign clk_out = clk_out_delayed;
  assign data_out = data_out_delayed;
  
endmodule