
module register_bank (
  input clock,
  input [31:0] data,
  input [4:0] rdaddress,
  input [4:0] wraddress,
  input wren,
  output reg [31:0] q
);

  reg [31:0] ram_q;

  always @(posedge clock) begin
    if (wren) begin
      ram_q <= data;
    end
    q <= ram_q;
  end

endmodule
