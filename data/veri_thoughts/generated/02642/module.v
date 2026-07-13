
module top_module (
  // inputs:
  input        clk,
  input  [7:0] address,
  input  [3:0] byteenable,
  input        wren,
  input  [31:0] data_in,
  
  // outputs:
  output [31:0] data_out
);

  reg [31:0] ram_data_out;

  always @(*) begin
    if(wren) begin
      ram_data_out <= data_in;
    end
    else begin
      ram_data_out <= ram_q;
    end
  end

  reg [31:0] ram_q;

  always @(posedge clk) begin
    ram_q <= ram_data_out;
  end

  assign data_out = ram_q;

endmodule