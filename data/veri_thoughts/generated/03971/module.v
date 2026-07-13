
module DECODER (
  input INA, INB, INC,
  output TWOPOS, TWONEG, ONEPOS, ONENEG
);

assign TWOPOS = ~(INA & INB & (~INC));
assign TWONEG = ~(~((~INA) & (~INB) & INC));
assign ONEPOS = ((~INA & INB & (~INC)) | ((~INC) & (~INB) & INA));
assign ONENEG = ((INA & (~INB) & INC) | (INC & INB & (~INA)));

endmodule
