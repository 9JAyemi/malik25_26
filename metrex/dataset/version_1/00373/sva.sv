// SVA checker for scrambler
// Bind into DUT: bind scrambler scrambler_sva #( .WIDTH(WIDTH) ) u_scrambler_sva (.*);

module scrambler_sva #(
  parameter int WIDTH = 512,
  parameter logic [57:0] SCRAM_INIT = 58'h3ff_ffff_ffff_ffff
)(
  input  logic                   clk,
  input  logic                   arst,
  input  logic                   ena,
  input  logic [WIDTH-1:0]       din,
  input  logic [WIDTH-1:0]       dout,
  input  logic [57:0]            scram_state
);

  // Golden model for next dout/state from current din/state
  function automatic void compute_next(
    input  logic [WIDTH-1:0] din_i,
    input  logic [57:0]      state_i,
    output logic [WIDTH-1:0] dout_o,
    output logic [57:0]      state_o
  );
    logic [WIDTH+58-1:0] hist;
    hist[57:0] = state_i;
    for (int i = 58; i < WIDTH+58; i++) begin
      hist[i] = hist[i-58] ^ hist[i-39] ^ din_i[i-58];
    end
    dout_o   = hist[WIDTH+58-1:58];
    state_o  = hist[WIDTH+58-1:WIDTH];
  endfunction

  logic [WIDTH-1:0] exp_dout;
  logic [57:0]      exp_state;
  always_comb compute_next(din, scram_state, exp_dout, exp_state);

  // Async reset drives known reset values immediately
  a_reset_async: assert property (@(posedge arst)
    (dout == '0) && (scram_state == SCRAM_INIT)
  );

  // While reset is asserted on clk edge, registers hold reset values
  a_reset_sync: assert property (@(posedge clk)
    arst |-> ((dout == '0) && (scram_state == SCRAM_INIT))
  );

  // When not enabled, hold last values
  a_hold_when_not_ena: assert property (@(posedge clk) disable iff (arst)
    !ena |-> (dout == $past(dout) && scram_state == $past(scram_state))
  );

  // When enabled, update matches golden model in the same cycle
  a_update_when_ena: assert property (@(posedge clk) disable iff (arst)
    ena |-> (dout == exp_dout && scram_state == exp_state)
  );

  // Any change must be due to enable
  a_change_requires_ena: assert property (@(posedge clk) disable iff (arst)
    ($changed(dout) || $changed(scram_state)) |-> $past(ena)
  );

  // No X/Z on state or output when out of reset
  a_no_x: assert property (@(posedge clk) disable iff (arst)
    !$isunknown({dout, scram_state})
  );

  // Coverage
  c_reset:           cover property (@(posedge arst) 1);
  c_one_update:      cover property (@(posedge clk) disable iff (arst) ena);
  c_two_updates:     cover property (@(posedge clk) disable iff (arst) ena ##1 ena);
  c_idle_stretch:    cover property (@(posedge clk) disable iff (arst) !ena ##1 !ena);

endmodule

// Recommended bind (put in a separate bind file or a package included in sim)
// bind scrambler scrambler_sva #(.WIDTH(WIDTH)) u_scrambler_sva (.*);