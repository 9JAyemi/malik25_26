
module TLU (EN, SE, CK, Q);
  input EN, SE, CK;
  output Q;

  reg Q;

  always @(posedge CK)
  begin
    if (EN)
      Q <= SE;
  end
endmodule