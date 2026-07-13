module phase_detector (
  input clk, 
  input ref,
  input in,
  output reg error
);

reg ref_reg, in_reg;

always @(posedge clk) begin
  ref_reg <= ref;
  in_reg <= in;
end

always @(posedge clk) begin
  error <= ref_reg ^ in_reg; 
end

endmodule


