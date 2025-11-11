// SVA for lights_switches
module lights_switches_sva (
  input         clk,
  input         reset_n,
  input  [1:0]  address,
  input  [7:0]  in_port,
  input  [7:0]  data_in,
  input  [7:0]  read_mux_out,
  input         clk_en,
  input  [31:0] readdata
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Structural/comb checks
  assert property (clk_en == 1'b1);
  assert property (data_in == in_port);
  assert property (read_mux_out == ((address == 2'b00) ? data_in : 8'h00));

  // While reset asserted, output is 0 (asynch reset)
  assert property (disable iff (1'b0) @(posedge clk) !reset_n |-> (readdata == 32'h0));

  // Registered behavior: 1-cycle latency, zero-extend to 32b
  assert property (
    readdata == {24'h0, ($past(address,1,!reset_n) == 2'b00 ? $past(in_port,1,!reset_n) : 8'h00)}
  );

  // Upper bits always zero when not in reset
  assert property (readdata[31:8] == 24'h0);

  // If previous address != 0, readback must be 0
  assert property (($past(address,1,!reset_n) != 2'b00) |-> (readdata == 32'h0));

  // No X/Z on output when inputs are known
  assert property ((reset_n && !$isunknown({address,in_port})) |-> !$isunknown(readdata));

  // Coverage
  cover property (disable iff (1'b0) @(posedge clk) !reset_n ##1 reset_n);
  cover property (address == 2'b00 ##1 (readdata[7:0] == $past(in_port,1,!reset_n)));
  cover property (address != 2'b00 ##1 (readdata == 32'h0));
  cover property (address == 2'b00 && $changed(in_port) ##1 readdata[7:0] == $past(in_port,1,!reset_n));
endmodule

bind lights_switches lights_switches_sva u_lights_switches_sva (
  .clk         (clk),
  .reset_n     (reset_n),
  .address     (address),
  .in_port     (in_port),
  .data_in     (data_in),
  .read_mux_out(read_mux_out),
  .clk_en      (clk_en),
  .readdata    (readdata)
);