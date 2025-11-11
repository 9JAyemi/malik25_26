// SVA for jt51_sh. Bind into the DUT; checks reset, hold, shift, and end-to-end behavior.
// Focused, parameter-aware, and concise.

`ifndef SYNTHESIS
module jt51_sh_sva #(parameter int width=5, stages=32, rstval=1'b0)
(
  input logic                  rst,
  input logic                  clk,
  input logic                  cen,
  input logic [width-1:0]      din,
  input logic [width-1:0]      drop
);

  default clocking cb @ (posedge clk); endclocking

  // Per-bit structural and step properties
  genvar i;
  generate
    for (i=0; i<width; i++) begin : GEN_SVA_BIT

      // Drop must reflect MSB of internal shift register
      assert property (drop[i] == bits[i][stages-1]);

      // On reset (at clock), register is cleared/filled and drop reflects rstval
      assert property (rst |-> (bits[i] == {stages{rstval}}) && (drop[i] == rstval));

      // Hold behavior when cen==0
      assert property (disable iff (rst) !cen |-> bits[i] == $past(bits[i]));
      assert property (disable iff (rst) !cen |-> drop[i] == $past(drop[i]));

      // Next-state update when cen==1
      if (stages == 1) begin
        assert property (disable iff (rst) cen |-> bits[i] == din[i]);
        assert property (disable iff (rst) cen |-> drop[i] == din[i]);
      end
      else begin
        assert property (disable iff (rst) cen
                         |-> bits[i] == { $past(bits[i][stages-2:0]), $past(din[i]) });
      end

    end
  endgenerate

  // End-to-end functional check with consecutive enables
  if (stages == 1) begin
    assert property (disable iff (rst) cen |-> drop == din);
  end
  else begin
    sequence consec_shifts; cen [*stages]; endsequence
    assert property (disable iff (rst) consec_shifts |-> drop == $past(din, stages-1));
  end

  // After reset deassertion, drop must hold rstval for at least 'stages' clocks
  assert property ($fell(rst) |-> (drop == {width{rstval}}) [*stages]);

  // No X on outputs when active
  assert property (disable iff (rst) !$isunknown(drop));

  // Coverage
  cover property ($rose(rst));
  cover property ($fell(rst));
  cover property (disable iff (rst) cen);                         // see an enable
  if (stages > 1) cover property (disable iff (rst) cen [*stages]); // see a full pipeline of enables
  cover property (disable iff (rst) !cen ##1 cen);                // stall then shift
  cover property (disable iff (rst) $changed(drop));              // drop activity

endmodule

bind jt51_sh jt51_sh_sva #(.width(width), .stages(stages), .rstval(rstval)) (.*);
`endif