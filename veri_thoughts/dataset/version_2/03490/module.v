module SSCG (
  input ref_clk,
  input modulation,
  output ssc_clk
);

parameter f_nom = 10000; // nominal frequency of the output clock signal
parameter f_delta = 100; // frequency deviation due to spread spectrum modulation
parameter f_spread = 1000; // modulation frequency of the spread spectrum modulation
parameter clk_div = 10; // clock divider ratio to reduce the frequency of the reference clock signal

reg [31:0] counter;
reg [31:0] mod_counter;
reg [31:0] delta_counter;
reg [31:0] delta;
reg [31:0] ssc_clk_counter;

wire [31:0] mod_signal;
wire [31:0] delta_signal;

assign mod_signal = (mod_counter < (f_spread / 2)) ? mod_counter : (f_spread - mod_counter);
assign delta_signal = delta * mod_signal;

assign ssc_clk = (ssc_clk_counter < (f_nom / 2)) ? 1'b0 : 1'b1;

always @(posedge ref_clk) begin
  if (counter == clk_div - 1) begin
    counter <= 0;
    mod_counter <= mod_counter + 1;
    delta_counter <= delta_counter + 1;
    if (delta_counter == delta_signal) begin
      delta_counter <= 0;
      delta <= delta + f_delta;
    end
    if (mod_counter == f_spread) begin
      mod_counter <= 0;
    end
    ssc_clk_counter <= ssc_clk_counter + 1;
    if (ssc_clk_counter == f_nom) begin
      ssc_clk_counter <= 0;
    end
  end else begin
    counter <= counter + 1;
  end
end

endmodule