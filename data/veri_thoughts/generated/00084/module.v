module constant_voltage_driver (
  input control,
  input [7:0] vref,
  output reg vout
);


  always @ (control, vref) begin
    if (control) begin
      vout <= vref;
    end else begin
      vout <= 0;
    end
  end
  
endmodule