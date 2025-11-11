// SVA for cic_filter. Bind this to the DUT.
// Focus: reset behavior, integrator accumulate, comb pipeline, decimator/interpolator control, output update timing.

module cic_filter_sva #(
  parameter int N = 3,
  parameter int R = 4,
  parameter int M = 16
)(
  input  logic              clk,
  input  logic              rst,
  input  logic [M-1:0]      in,
  input  logic [M-1:0]      out,

  // internal DUT registers
  input  logic [M-1:0]      integrator_reg,
  input  logic [M-1:0]      comb_reg [0:N-1],
  input  logic [M-1:0]      decimator_reg,
  input  logic [M-1:0]      interpolator_reg,
  input  logic [M-1:0]      out_reg
);

  default clocking cb @ (posedge clk); endclocking
  // Assertions below that use |-> or $past() guard with $past(!rst, depth) where needed.
  // Others use explicit non-overlapped reset checks.

  // Reset clears all state next cycle
  assert property (@cb rst |=> integrator_reg==0 && decimator_reg==0 && interpolator_reg==0 && out_reg==0)
    else $error("Reset did not clear primary registers");
  genvar gi_rst;
  generate
    for (gi_rst=0; gi_rst<N; gi_rst++) begin : G_RST_CLR
      assert property (@cb rst |=> comb_reg[gi_rst]==0)
        else $error("Reset did not clear comb_reg[%0d]", gi_rst);
    end
  endgenerate

  // Output port equals out_reg always
  assert property (@cb out == out_reg) else $error("out port != out_reg");

  // Integrator accumulates input (modulo M bits)
  assert property (@cb disable iff (rst) $past(!rst) |-> integrator_reg == $past(integrator_reg) + $past(in))
    else $error("Integrator accumulation mismatch");

  // Comb pipeline: stage 0 captures prior integrator; other stages shift
  assert property (@cb disable iff (rst) $past(!rst) |-> comb_reg[0] == $past(integrator_reg))
    else $error("Comb stage 0 mismatch");
  genvar gi;
  generate
    for (gi=1; gi<N; gi++) begin : G_COMB_SHIFT
      assert property (@cb disable iff (rst) $past(!rst) |-> comb_reg[gi] == $past(comb_reg[gi-1]))
        else $error("Comb shift mismatch at stage %0d", gi);
    end
  endgenerate

  // End-to-end comb latency check (N cycles)
  assert property (@cb disable iff (rst) $past(!rst, N) |-> comb_reg[N-1] == $past(integrator_reg, N))
    else $error("Comb end-to-end latency/value mismatch");

  // Decimator / Interpolator control and output timing
  if (R > 1) begin : G_DECIM

    // Counter stays in range [0, R-1]
    assert property (@cb disable iff (rst) decimator_reg < R)
      else $error("Decimator counter out of range");

    // Normal increment and hold output when not wrapping
    assert property (@cb disable iff (rst)
      $past(!rst) && ($past(decimator_reg) != R-1) |-> (decimator_reg == $past(decimator_reg)+1 && out_reg == $past(out_reg)))
      else $error("Decimator increment or out hold error");

    // Wrap and update output on terminal count
    assert property (@cb disable iff (rst)
      $past(!rst) && ($past(decimator_reg) == R-1) |-> (decimator_reg == '0 && out_reg == $past(comb_reg[N-1])))
      else $error("Decimator wrap or out update error");

    // Output only changes on wrap
    assert property (@cb disable iff (rst) $changed(out_reg) |-> $past(decimator_reg) == R-1)
      else $error("out_reg changed outside decimation boundary");

    // Coverage: see a wrap and output update
    cover property (@cb disable iff (rst)
      decimator_reg == (R-2) ##1 decimator_reg == (R-1) ##1 (decimator_reg=='0 && out_reg == $past(comb_reg[N-1])));

  end else begin : G_INTERP // R <= 1 (effectively R==1)

    // Interpolator counter sticks at 0; output updates every cycle
    assert property (@cb disable iff (rst) interpolator_reg == '0)
      else $error("Interpolator counter not zero for R<=1");
    assert property (@cb disable iff (rst) $past(!rst) |-> out_reg == $past(comb_reg[N-1]))
      else $error("out_reg not updating every cycle for R<=1");

    // Coverage: observe output activity
    cover property (@cb disable iff (rst) $changed(out_reg));

  end

endmodule

// Bind to DUT (connect internals)
bind cic_filter cic_filter_sva #(.N(N), .R(R), .M(M)) cic_filter_sva_i (
  .clk(clk),
  .rst(rst),
  .in(in),
  .out(out),
  .integrator_reg(integrator_reg),
  .comb_reg(comb_reg),
  .decimator_reg(decimator_reg),
  .interpolator_reg(interpolator_reg),
  .out_reg(out_reg)
);