module flag_register(
  input IN_FLAG,
  input LD,
  input SET,
  input CLR,
  input CLK,
  output reg OUT_FLAG
);

  always @(posedge CLK) begin
    if (LD) begin
      OUT_FLAG <= IN_FLAG;
    end else if (SET) begin
      OUT_FLAG <= 1;
    end else if (CLR) begin
      OUT_FLAG <= 0;
    end
  end

endmodule