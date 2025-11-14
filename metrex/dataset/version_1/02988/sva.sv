// SVA for tg_prbs_gen
// Bindable, concise, and focused on functional/temporal checks and coverage.

module tg_prbs_gen_sva #
(
  parameter int PRBS_WIDTH = 64,
  parameter int PRBS_OFFSET = 0,
  parameter logic [PRBS_WIDTH-1:0] TAPS = 32'h8020_0003
)
(
  // DUT ports
  input  logic                    clk_i,
  input  logic                    clk_en,
  input  logic                    rst,
  input  logic [PRBS_WIDTH-1:0]   prbs_seed_i,
  input  logic                    initialize_done,
  input  logic [PRBS_WIDTH-1:0]   prbs_o,
  input  logic [3:0]              prbs_shift_value,
  input  logic [31:0]             ReSeedcounter_o,

  // DUT internals (bound explicitly)
  input  logic [PRBS_WIDTH-1:0]   Next_LFSR_Reg,
  input  logic [PRBS_WIDTH-1:0]   LFSR_Reg,
  input  logic [PRBS_WIDTH-1:0]   counterA,
  input  logic                    Bits0_9_zero,
  input  logic                    Feedback,
  input  logic [PRBS_WIDTH-1:0]   ReSeedcounter,
  input  logic [10:0]             freerun_counters,
  input  logic                    init_setup,
  input  logic                    prbs_clk_en1,
  input  logic                    prbs_clk_en2
);

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst);

  function automatic logic [PRBS_WIDTH-1:0] ref_next_lfsr
    (input logic [PRBS_WIDTH-1:0] cur, input logic fb);
    logic [PRBS_WIDTH-1:0] n;
    for (int i = PRBS_WIDTH-1; i >= 1; i--) begin
      n[i] = cur[i-1] ^ (TAPS[i-1] ? fb : 1'b0);
    end
    n[0] = fb;
    return n;
  endfunction

  // Reset-time checks (not disabled during rst)
  assert property (@(posedge clk_i) rst |-> (
      freerun_counters == '0 &&
      counterA         == '0 &&
      ReSeedcounter    == '0 &&
      init_setup       == 1'b0 &&
      LFSR_Reg[3:0]               == (prbs_seed_i[3:0] | 4'h5) &&
      LFSR_Reg[PRBS_WIDTH-1:4]    == prbs_seed_i[PRBS_WIDTH-1:4]
  ));

  // Clock-enable correctness
  assert property (prbs_clk_en1 == prbs_clk_en2);
  assert property (prbs_clk_en1 == (clk_en | init_setup));
  assert property (init_setup |-> prbs_clk_en1);

  // Initialize_done is complement of init_setup
  assert property (initialize_done == ~init_setup);

  // init_setup reflects freerun threshold
  assert property (init_setup == (freerun_counters <= (PRBS_OFFSET + 255)));

  // freerun_counters behavior
  assert property ((freerun_counters <= 11'd128 || init_setup) |=> freerun_counters == $past(freerun_counters) + 11'd1);
  assert property (!(freerun_counters <= 11'd128 || init_setup) |=> freerun_counters == $past(freerun_counters));

  // counterA behavior
  assert property ( prbs_clk_en1 |=> counterA == $past(counterA) + 1'b1 );
  assert property (!prbs_clk_en1 |=> counterA == $past(counterA));

  // ReSeedcounter behavior
  assert property ( prbs_clk_en1 && (ReSeedcounter != {PRBS_WIDTH{1'b1}}) |=> ReSeedcounter == $past(ReSeedcounter) + 1'b1 );
  assert property ( prbs_clk_en1 && (ReSeedcounter == {PRBS_WIDTH{1'b1}}) |=> ReSeedcounter == '0 );
  assert property (!prbs_clk_en1 |=> ReSeedcounter == $past(ReSeedcounter));

  // ReSeedcounter_o mapping (only when PRBS_WIDTH <= 32)
  if (PRBS_WIDTH <= 32) begin
    assert property (ReSeedcounter_o[PRBS_WIDTH-1:0] == ReSeedcounter);
    assert property (ReSeedcounter_o[31:PRBS_WIDTH] == '0);
  end

  // LFSR combinational correctness
  assert property (Bits0_9_zero == ~(|LFSR_Reg[PRBS_WIDTH-2:0]));
  assert property (Feedback == (LFSR_Reg[PRBS_WIDTH-1] ^ Bits0_9_zero));
  assert property (Next_LFSR_Reg == ref_next_lfsr(LFSR_Reg, Feedback));

  // LFSR sequential step on enable
  assert property (prbs_clk_en2 |=> LFSR_Reg == ref_next_lfsr($past(LFSR_Reg), $past(Feedback)));

  // LFSR never all zeros after reset
  assert property (LFSR_Reg != '0);

  // prbs output mirrors LFSR_Reg
  assert property (prbs_o == LFSR_Reg);

  // prbs_shift_value behavior
  assert property ( prbs_clk_en2 |=> prbs_shift_value == { $past(prbs_shift_value[2:0]), $past(LFSR_Reg[PRBS_WIDTH-1]) } );
  assert property (!prbs_clk_en2 |=> prbs_shift_value == $past(prbs_shift_value));

  // Known outputs after reset deassertion
  assert property (!$isunknown({initialize_done, prbs_o, prbs_shift_value, ReSeedcounter_o}));

  // Coverage
  cover property ($fell(init_setup));                       // initialization finished
  cover property (init_setup && !clk_en);                   // gating via init_setup
  cover property (!init_setup && clk_en && prbs_clk_en2);   // gating via clk_en
  cover property (prbs_clk_en1 && ReSeedcounter == {PRBS_WIDTH{1'b1}} ##1 ReSeedcounter == '0); // wrap
  cover property (Bits0_9_zero);                            // special feedback path exercised
endmodule

// Example bind (place in a separate bind file or testbench)
// Ensures access to DUT internals needed by the SVA.
bind tg_prbs_gen tg_prbs_gen_sva #(
  .PRBS_WIDTH(PRBS_WIDTH),
  .PRBS_OFFSET(PRBS_OFFSET),
  .TAPS(TAPS)
) tg_prbs_gen_sva_i (
  .*,
  .Next_LFSR_Reg(Next_LFSR_Reg),
  .LFSR_Reg(LFSR_Reg),
  .counterA(counterA),
  .Bits0_9_zero(Bits0_9_zero),
  .Feedback(Feedback),
  .ReSeedcounter(ReSeedcounter),
  .freerun_counters(freerun_counters),
  .init_setup(init_setup),
  .prbs_clk_en1(prbs_clk_en1),
  .prbs_clk_en2(prbs_clk_en2)
);