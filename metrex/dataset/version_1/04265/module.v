module Counter32 (
  
  input Reset_n_i,
  
  input Clk_i,
  
  input ResetSig_i,
  
  input Preset_i,
  
  input Enable_i,
  
  input Direction_i,
  
  input[15:0] PresetValH_i,
  
  input[15:0] PresetValL_i,
  
  output[15:0] DH_o,
  
  output[15:0] DL_o,
  
  output Overflow_o,
  
  output Zero_o
);

  reg [32:0] Value;

  always @(negedge Reset_n_i or posedge Clk_i)
  begin
    if (!Reset_n_i)
    begin
      Value   <= 'd0;
    end
    else
    begin
      if (ResetSig_i)
        Value <= 'd0;
      else if (Preset_i)
        Value <= {1'b0, PresetValH_i, PresetValL_i};
      else if (Enable_i)
      begin
        if (!Direction_i)
          Value <= {1'b0, Value[31:0]} + 1'b1;
        else
          Value <= {1'b0, Value[31:0]} - 1'b1;
      end
    end
  end

  assign DH_o = Value[31:16];
  assign DL_o = Value[15:0];

  assign Zero_o = (Value[31:0] == 'd0 ? 1'b1 : 1'b0);

  assign Overflow_o = Value[32];

endmodule
