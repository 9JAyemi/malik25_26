// SVA for up_counter — concise, high-quality checks and coverage
module up_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        load,
  input  logic [3:0]  data_in,
  input  logic [3:0]  data_out
);

  // past_valid to safely use $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  A_NO_X_OUT:    assert property (cb !$isunknown(data_out));
  A_NO_X_CTRL:   assert property (cb !$isunknown({reset, load}));
  A_NO_X_DIN_ON_LOAD:
                 assert property (cb past_valid && $past(load) && !$past(reset) |-> !$isunknown($past(data_in)));

  // Next-state functional correctness (priority: reset > load > increment)
  A_RESET:       assert property (cb past_valid && $past(reset) |-> data_out == 4'h0);
  A_LOAD:        assert property (cb past_valid && !$past(reset) && $past(load)
                                   |-> data_out == $past(data_in));
  A_INC:         assert property (cb past_valid && !$past(reset) && !$past(load)
                                   |-> data_out == ($past(data_out) + 4'd1));
  // Explicit wrap check (redundant with A_INC, but targeted)
  A_WRAP:        assert property (cb past_valid && !$past(reset) && !$past(load) && $past(data_out)==4'hF
                                   |-> data_out == 4'h0);

  // Coverage
  C_RESET:       cover property (cb past_valid && $past(reset));
  C_LOAD:        cover property (cb past_valid && !$past(reset) && $past(load) && data_out == $past(data_in));
  C_INC:         cover property (cb past_valid && !$past(reset) && !$past(load));
  C_WRAP:        cover property (cb past_valid && !$past(reset) && !$past(load) && $past(data_out)==4'hF && data_out==4'h0);
  C_RST_LOAD_PRIO: cover property (cb past_valid && $past(reset && load) && data_out == 4'h0);

endmodule

// Bind into DUT
bind up_counter up_counter_sva sva_up_counter (
  .clk(clk),
  .reset(reset),
  .load(load),
  .data_in(data_in),
  .data_out(data_out)
);