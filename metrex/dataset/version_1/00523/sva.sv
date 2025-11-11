// SVA checker for CIC. Bind this to the DUT. Focused, high-signal-coverage.
module CIC_sva #(parameter int n=2, m=2, r=2, N=2);
  // Bound into CIC scope; can directly see clk, in, out and internal regs.
  default clocking cb @(posedge clk); endclocking

  // Start tracking after first clock to allow $past
  bit started;
  always @(posedge clk) started <= 1'b1;

  // Basic parameter sanity (counter is 8b; r must fit and be >=1)
  assert property (started |-> (r >= 1 && r <= 256))
    else $error("CIC: r must be in [1..256], got %0d", r);

  // Counter behavior
  assert property (disable iff (!started) ($past(counter) == r-1) |-> (counter == 8'(0)))
    else $error("CIC: counter must reset to 0 after r-1");
  assert property (disable iff (!started) ($past(counter) != r-1) |-> (counter == $past(counter)+1))
    else $error("CIC: counter must increment when not at r-1");

  // Decimation register updates
  assert property (disable iff (!started) ($past(counter) == r-1) |-> (decimated_input == $past(in)))
    else $error("CIC: decimated_input must capture in when counter hits r-1");
  assert property (disable iff (!started) ($past(counter) != r-1) |-> (decimated_input == $past(decimated_input)))
    else $error("CIC: decimated_input must hold when counter not r-1");
  assert property (disable iff (!started) $changed(decimated_input) |-> ($past(counter) == r-1))
    else $error("CIC: decimated_input changed outside decimation event");
  // After a change, it must remain stable for the next r-1 cycles
  assert property (disable iff (!started)
                   $changed(decimated_input) |-> $stable(decimated_input)[*(r-1)])
    else $error("CIC: decimated_input not stable for r-1 cycles after update");

  // Integrator stage
  assert property (disable iff (!started) integrator_input == $past(decimated_input))
    else $error("CIC: integrator_input must be decimated_input (1-cycle pipeline)");
  assert property (disable iff (!started) integrator_output == $past(integrator_output) + $past(integrator_input))
    else $error("CIC: integrator_output must accumulate integrator_input");

  // Comb stage
  assert property (disable iff (!started) comb_input == $past(integrator_output))
    else $error("CIC: comb_input must be integrator_output (1-cycle pipeline)");
  assert property (disable iff (!started) comb_output == $past(comb_input) - $past(comb_output))
    else $error("CIC: comb_output must be previous comb_input minus previous comb_output");

  // Output mapping (handle width mismatch explicitly)
  generate
    if (m == n) begin
      assert property (out == comb_output)
        else $error("CIC: out must equal comb_output when m==n");
    end else if (m < n) begin
      assert property (out == comb_output[m-1:0])
        else $error("CIC: out must be truncated LSBs of comb_output when m<n");
    end else begin : WEXP
      localparam int PAD = m-n;
      assert property (out == { {PAD{1'b0}}, comb_output })
        else $error("CIC: out must be zero-extended comb_output when m>n");
    end
  endgenerate

  // X-propagation checks (post-start)
  assert property (disable iff (!started) !$isunknown(counter))
    else $error("CIC: counter is X/Z");
  assert property (disable iff (!started) !$isunknown(decimated_input))
    else $error("CIC: decimated_input is X/Z");
  assert property (disable iff (!started) !$isunknown(integrator_input))
    else $error("CIC: integrator_input is X/Z");
  assert property (disable iff (!started) !$isunknown(integrator_output))
    else $error("CIC: integrator_output is X/Z");
  assert property (disable iff (!started) !$isunknown(comb_input))
    else $error("CIC: comb_input is X/Z");
  assert property (disable iff (!started) !$isunknown(comb_output))
    else $error("CIC: comb_output is X/Z");
  assert property (disable iff (!started) !$isunknown(out))
    else $error("CIC: out is X/Z");

  // Functional coverage
  cover property (disable iff (!started) ($past(counter)==r-1) and (counter==0));
  cover property (disable iff (!started) $changed(decimated_input));
  cover property (disable iff (!started) $changed(integrator_output));
  cover property (disable iff (!started) $changed(comb_output));
endmodule

// Bind into the DUT
bind CIC CIC_sva #(.n(n), .m(m), .r(r), .N(N)) CIC_sva_i();