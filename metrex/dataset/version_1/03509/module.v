module and_gate(input a, b, clk, output reg out);
  wire mux_out;
  reg d_ff_out;
  
  // Multiplexer implementation
  assign mux_out = (a & b);
  
  // D flip-flop implementation
  always @(posedge clk) begin
    d_ff_out <= mux_out;
  end
  
  always @* begin
    out = d_ff_out;
  end
endmodule