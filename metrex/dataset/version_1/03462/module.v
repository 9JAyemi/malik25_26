
module glitch_free_mux #(
  parameter n = 4 // number of clock signals
) (
  input [n-1:0] clk,
  input sel,
  output reg sys_clk 
);

reg [n-1:0] prev_clk; // previous clock signal
reg [n-1:0] cur_clk; // current clock signal

always @ (posedge clk[0]) begin // Use a single edge-sensitive clock for the first always block
  if (sel) begin
    prev_clk <= cur_clk;
    cur_clk <= clk;
  end
end

always @* begin // Use an always block to assign `sys_clk`
  sys_clk = (cur_clk == prev_clk) ? cur_clk : prev_clk;
end

endmodule