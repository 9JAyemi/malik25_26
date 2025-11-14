module TDC (
  input clk,
  input in1,
  input in2,
  output reg [15:0] out
);

parameter resolution = 1; // resolution of the TDC in picoseconds

reg in1_prev, in2_prev;
reg [15:0] count;

always @(posedge clk) begin
  if (in1 && !in1_prev) begin
    count <= 0;
  end else if (in2 && !in2_prev) begin
    out <= count * resolution;
  end else begin
    count <= count + 1;
  end
  in1_prev <= in1;
  in2_prev <= in2;
end

endmodule