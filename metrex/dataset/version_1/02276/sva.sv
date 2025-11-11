// SVA for falling_edge_detector
module falling_edge_detector_sva #(parameter WIDTH=32) (
  input logic                  clk,
  input logic                  reset,   // active-low
  input logic [WIDTH-1:0]      in,
  input logic [WIDTH-1:0]      out
);
  // Helper: current LSB-onehot of input
  let lsb = (in ^ (in & (in - 1)));

  // Reset behavior
  assert property (@(posedge clk) !reset |-> out == '0);
  assert property (@(negedge reset) out == '0);

  // Functional next-state relation (valid when previous cycle not in reset)
  assert property (@(posedge clk) disable iff (!reset)
                   $past(reset) |-> out == (lsb & ~ $past(out)));

  // Output constraints
  assert property (@(posedge clk) disable iff (!reset) $onehot0(out));
  assert property (@(posedge clk) disable iff (!reset) (out & ~lsb) == '0);

  // LSB extractor sanity
  assert property (@(posedge clk) (in == '0) |-> (lsb == '0));
  assert property (@(posedge clk) (in != '0) |-> $onehot(lsb));

  // Per-bit pulses are single-cycle
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : g_bit_pulse
      assert property (@(posedge clk) disable iff (!reset) out[i] |=> !out[i]);
    end
  endgenerate

  // X checks (optional but recommended)
  assert property (@(posedge clk) !$isunknown(reset));
  assert property (@(posedge clk) disable iff (!reset) !$isunknown(in));
  assert property (@(posedge clk) disable iff (!reset) !$isunknown(out));

  // Coverage
  cover property (@(posedge clk) $rose(reset) ##1 out != '0);
  cover property (@(posedge clk) disable iff (!reset) out != '0);
  cover property (@(posedge clk) disable iff (!reset) out[0]);
  cover property (@(posedge clk) disable iff (!reset) out[WIDTH-1]);
  cover property (@(posedge clk) disable iff (!reset)
                  (out != '0) ##1 ((out != '0) && (out != $past(out))));
endmodule

bind falling_edge_detector falling_edge_detector_sva #(.WIDTH(32))
  falling_edge_detector_sva_i (.clk(clk), .reset(reset), .in(in), .out(out));