// SVA for jt12_eg_ctrl
// Bind example (add in TB): bind jt12_eg_ctrl jt12_eg_ctrl_sva sva(.clk(clk), .rst_n(rst_n), .*);

module jt12_eg_ctrl_sva (
  input logic clk, rst_n,

  // DUT ports
  input logic              keyon_now,
  input logic              keyoff_now,
  input logic       [2:0]  state_in,
  input logic       [9:0]  eg,
  input logic       [4:0]  arate, rate1, rate2,
  input logic       [3:0]  rrate,
  input logic       [3:0]  sl,
  input logic              ssg_en,
  input logic       [2:0]  ssg_eg,
  input logic              ssg_inv_in,

  input logic              ssg_inv_out,
  input logic       [4:0]  base_rate,
  input logic       [2:0]  state_next,
  input logic              pg_rst
);

  // Local encodings (match DUT)
  localparam logic [2:0] ATTACK  = 3'b001;
  localparam logic [2:0] DECAY   = 3'b010;
  localparam logic [2:0] HOLD    = 3'b100;
  localparam logic [2:0] RELEASE = 3'b000;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Derived expected terms
  let sustain_exp = (sl == 4'd15) ? 5'h1f : {1'b0, sl};
  let ssg_att     = ssg_eg[2];
  let ssg_alt     = ssg_eg[1];
  let ssg_hold    = ssg_eg[0] & ssg_en;
  let ssg_over    = ssg_en & eg[9];
  let ssg_pg_rst  = ssg_over & !(ssg_alt || ssg_hold);
  let pg_rst_exp  = keyon_now | ssg_pg_rst;

  let P_KEYON = (!keyoff_now && keyon_now);
  let P_ATT   = (!keyoff_now && !keyon_now && (state_in == ATTACK));
  let P_DEC   = (!keyoff_now && !keyon_now && (state_in == DECAY));
  let P_HOLD  = (!keyoff_now && !keyon_now && (state_in == HOLD));
  let P_DEF   = !(P_KEYON || P_ATT || P_DEC || P_HOLD);

  // Basic sanity: outputs defined
  assert property (1'b1 |-> !$isunknown({base_rate, state_next, ssg_inv_out, pg_rst}));

  // pg_rst exact function
  assert property (1'b1 |-> (pg_rst == pg_rst_exp));

  // Key-on branch
  assert property (P_KEYON |-> (base_rate == arate
                                && state_next == ATTACK
                                && ssg_inv_out == (ssg_att & ssg_en)));

  // ATTACK branch
  assert property (P_ATT && (eg == 10'd0)
                   |-> (base_rate == rate1 && state_next == DECAY && ssg_inv_out == ssg_inv_in));
  assert property (P_ATT && (eg != 10'd0)
                   |-> (base_rate == arate && state_next == ATTACK && ssg_inv_out == ssg_inv_in));

  // DECAY: SSG overflow path
  assert property (P_DEC && ssg_over && ssg_hold
                   |-> (base_rate == 5'd0 && state_next == HOLD
                        && ssg_inv_out == (ssg_en & (ssg_alt ^ ssg_inv_in))));
  assert property (P_DEC && ssg_over && !ssg_hold
                   |-> (base_rate == arate && state_next == ATTACK
                        && ssg_inv_out == (ssg_en & (ssg_alt ^ ssg_inv_in))));

  // DECAY: normal path
  assert property (P_DEC && !ssg_over && (eg[9:5] >= sustain_exp)
                   |-> (base_rate == rate2 && state_next == DECAY && ssg_inv_out == ssg_inv_in));
  assert property (P_DEC && !ssg_over && (eg[9:5] <  sustain_exp)
                   |-> (base_rate == rate1 && state_next == DECAY && ssg_inv_out == ssg_inv_in));

  // HOLD branch
  assert property (P_HOLD |-> (base_rate == 5'd0 && state_next == HOLD && ssg_inv_out == ssg_inv_in));

  // Default branch (incl. keyoff or other states)
  assert property (P_DEF |-> (base_rate == {rrate, 1'b1} && state_next == RELEASE && ssg_inv_out == 1'b0));

  // Priority check: keyon and keyoff together go to default (RELEASE)
  assert property (keyon_now && keyoff_now |-> P_DEF);

  // --------------------
  // Coverage
  // --------------------
  cover property (P_KEYON);
  cover property (P_ATT && eg==10'd0);
  cover property (P_ATT && eg!=10'd0);
  cover property (P_DEC && ssg_over && ssg_hold);
  cover property (P_DEC && ssg_over && !ssg_hold);
  cover property (P_DEC && !ssg_over && (eg[9:5] >= sustain_exp));
  cover property (P_DEC && !ssg_over && (eg[9:5] <  sustain_exp));
  cover property (P_HOLD);
  cover property (P_DEF && keyoff_now);                 // release due to keyoff
  cover property (pg_rst && keyon_now);                 // pg_rst via keyon
  cover property (pg_rst && !keyon_now && ssg_pg_rst);  // pg_rst via SSG

endmodule