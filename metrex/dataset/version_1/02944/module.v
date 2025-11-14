module schmitt_trigger (
  input in,
  input Vt_high,
  input Vt_low,
  input Vdd,
  output out
);

  reg out_reg;
  reg prev_out_reg;
  
  always @ (in or prev_out_reg)
  begin
    if (prev_out_reg == 1'b0 && in >= Vt_high)
      out_reg = 1'b1;
    else if (prev_out_reg == 1'b1 && in <= Vt_low)
      out_reg = 1'b0;
    else
      out_reg = prev_out_reg;
  end
  
  assign out = out_reg;
  
  always @ (posedge Vdd)
  begin
    prev_out_reg <= out_reg;
  end
  
endmodule