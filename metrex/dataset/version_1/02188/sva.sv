// SVA for register_4bit
module register_4bit_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        load,
  input  logic [3:0]  data_in,
  input  logic [3:0]  Q
);

  default clocking cb @ (posedge clk); endclocking

  // Asynchronous reset: Q must be 0 whenever reset is high (at all sampled clocks)
  ap_reset_forces_zero: assert property (reset |-> (Q == 4'b0) throughout reset);

  // Optional immediate async check (tolerant of NBA timing)
  ap_async_reset_immediate: assert property (@(posedge reset) ##0 (Q == 4'b0));

  // On load, Q updates on the next clock to the sampled data_in
  ap_load_updates: assert property (disable iff (reset)
                                    load |=> (Q == $past(data_in)));

  // When not loading, Q holds its previous value
  ap_hold_when_no_load: assert property (disable iff (reset)
                                         !load |=> (Q == $past(Q)));

  // Any Q change (without reset involvement) must be caused by a prior load
  ap_change_implies_load: assert property (
    (!reset && !$past(reset) && (Q != $past(Q))) |-> $past(load)
  );

  // X/Z checks
  ap_no_x_on_ctrl_out: assert property (!$isunknown({reset, load, Q}));
  ap_no_x_data_when_used: assert property ((load && !reset) |-> !$isunknown(data_in));

  // Coverage
  cp_reset_assert:     cover property ($rose(reset));
  cp_reset_deassert:   cover property ($fell(reset));
  cp_load_update:      cover property (disable iff (reset) load |=> (Q == $past(data_in)));
  cp_hold_3cycles:     cover property (disable iff (reset) (!load && Q == $past(Q))[*3]);
  cp_two_back_to_back: cover property (disable iff (reset) load ##1 load);

endmodule

// Bind into DUT
bind register_4bit register_4bit_sva sva_i (
  .clk   (clk),
  .reset (reset),
  .load  (load),
  .data_in (data_in),
  .Q     (Q)
);