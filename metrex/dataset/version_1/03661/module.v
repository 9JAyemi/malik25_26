module VCO_interface (
  input in,
  input [7:0] vctrl,
  output reg out
);

parameter fmin = 1; // minimum frequency of the VCO
parameter fmax = 1000; // maximum frequency of the VCO
parameter vmin = 0; // minimum voltage of the VCO
parameter vmax = 255; // maximum voltage of the VCO

reg [31:0] count;
reg [31:0] freq;

always @ (posedge in) begin
  count <= count + 1;
  if (count >= freq) begin
    out <= ~out;
    count <= 0;
  end
end

always @ (vctrl) begin
  freq <= (vctrl - vmin) * (fmax - fmin) / (vmax - vmin) + fmin;
end

endmodule