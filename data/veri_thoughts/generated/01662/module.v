
module dff_preset_clear (
  output reg Q,
  input D,
  input C,
  input R,
  input P
);

  always @(posedge C) begin
    if (R)
      Q <= 1'b0;
    else if (P)
      Q <= 1'b1;
    else
      Q <= D;
  end

endmodule