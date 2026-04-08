module manchester (
  input in,
  output out
);

  reg prev_in;
  reg out_reg;
  
  always @(posedge in) begin
    if (in == prev_in) begin
      out_reg <= ~out_reg;
    end else begin
      out_reg <= in;
    end
    prev_in <= in;
  end
  
  assign out = out_reg;
  
endmodule