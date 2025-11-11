// SVA for top_module
// Bind this file to the DUT: bind top_module top_module_sva u_sva(.*);

module top_module_sva (
  input logic               clk,
  input logic               rst_n,
  input logic [1023:0]      in,
  input logic [7:0]         sel,
  input logic               rise,
  input logic               down,
  input logic [15:0]        out,
  input logic [3:0]         delay_sel,
  input logic [3:0]         delayed_in,
  input logic [3:0]         delayed_in_prev,
  input logic [3:0]         edge_rising,
  input logic [3:0]         edge_falling
);

  default clocking cb @(posedge clk); endclocking
  // Functional checks run only when out of reset
  default disable iff (!rst_n);

  // Reset values (asynchronous reset coverage on next clock)
  assert property (@(posedge clk) !rst_n |-> (delay_sel==4'h0 && delayed_in_prev==4'h0 && rise==1'b0 && down==1'b0 && out==16'h0000));

  // delay_sel should mirror sel[3:0]
  assert property (delay_sel == $past(sel[3:0]));

  // Upper sel bits must not affect selection
  assert property ((sel[3:0] == $past(sel[3:0]) && sel[7:4] != $past(sel[7:4])) |-> ($stable(delay_sel) && $stable(delayed_in)));

  // Mux correctness
  assert property (delayed_in == in[delay_sel*4 +: 4]);

  // Pipeline: delayed_in_prev holds previous delayed_in
  assert property (delayed_in_prev == $past(delayed_in));

  // Edge detection correctness
  assert property (($past(delayed_in) < delayed_in) |-> (edge_rising == delayed_in && edge_falling == 4'h0 && rise && !down));
  assert property (($past(delayed_in) > delayed_in) |-> (edge_falling == delayed_in && edge_rising == 4'h0 && down && !rise));
  assert property (($past(delayed_in) == delayed_in) |-> (edge_rising == 4'h0 && edge_falling == 4'h0 && !rise && !down));

  // Rising and falling cannot be simultaneous
  assert property (!(rise && down));

  // out update only when condition met; otherwise it holds
  assert property (rise && down && (out==16'h0000) |-> out == {1'b0, {11{edge_rising[3]}}, (edge_rising - edge_falling)});
  assert property (!(rise && down && (out==16'h0000)) |-> out == $past(out));

  // X-checks after coming out of reset
  assert property ($rose(rst_n) |=> (!$isunknown(delay_sel) && !$isunknown(delayed_in_prev) &&
                                     !$isunknown(edge_rising) && !$isunknown(edge_falling) &&
                                     !$isunknown(rise) && !$isunknown(down) && !$isunknown(out)));

  // Coverage
  cover property ($past(delayed_in) < delayed_in && rise);
  cover property ($past(delayed_in) > delayed_in && down);
  cover property ($changed(delay_sel));
  cover property (rise && down);                         // expected unreachable with current logic
  cover property (rise && down && (out==16'h0000));      // expected unreachable with current logic
  cover property (out != $past(out));

endmodule

bind top_module top_module_sva u_sva(
  .clk(clk), .rst_n(rst_n), .in(in), .sel(sel),
  .rise(rise), .down(down), .out(out),
  .delay_sel(delay_sel), .delayed_in(delayed_in),
  .delayed_in_prev(delayed_in_prev),
  .edge_rising(edge_rising), .edge_falling(edge_falling)
);