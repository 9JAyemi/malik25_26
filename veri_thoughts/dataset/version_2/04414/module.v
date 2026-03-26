module sparc_exu_aluspr (
  input [63:0] rs1_data,
  input [63:0] rs2_data,
  input cin,
  output reg [63:0] spr_out
);

  always @* begin
    // ALU operation
    spr_out = (cin) ? rs1_data + rs2_data : rs1_data - rs2_data;
  end

endmodule
