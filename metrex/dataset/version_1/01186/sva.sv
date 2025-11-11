// SVA for reg32_R0
module reg32_R0_sva(
  input logic        clk,
  input logic        clr,
  input logic        BA_out,
  input logic        write_enable,
  input logic [31:0] write_value,
  input logic [31:0] Rout
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Functional equivalence to RTL (write beats clear; write gated by !BA_out)
  property p_functional_update;
    past_valid |->
      Rout ==
        ( $past(write_enable && !BA_out) ? $past(write_value) :
          $past(clr)                    ? 32'h0              :
                                          $past(Rout) );
  endproperty
  assert property (p_functional_update);

  // Explicit priority when clr and allowed write are both asserted
  assert property (past_valid && $past(clr && write_enable && !BA_out) |-> Rout == $past(write_value));

  // Inhibited write (BA_out=1) holds value unless clear also asserted
  assert property (past_valid && $past(write_enable && BA_out && !clr) |-> Rout == $past(Rout));

  // X/Z hygiene
  assert property (!$isunknown(Rout));
  assert property (!$isunknown({clr, write_enable, BA_out}));
  assert property (past_valid && $past(write_enable && !BA_out) |-> !$isunknown($past(write_value)));

  // Coverage
  cover property (past_valid && $past(clr) && !$past(write_enable && !BA_out));            // clear-only
  cover property (past_valid && $past(write_enable && !BA_out));                           // write-only
  cover property (past_valid && $past(write_enable && BA_out) && !$past(clr));             // write inhibited
  cover property (past_valid && $past(clr && write_enable && !BA_out));                    // clr + write (write wins)
  cover property (past_valid && !$past(clr) && !$past(write_enable) && $stable(Rout));     // hold path

endmodule

// Bind into DUT
bind reg32_R0 reg32_R0_sva sva_i(.*);