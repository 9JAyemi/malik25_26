// SVA for arbiter
// Bind into the DUT: bind arbiter arbiter_sva sva(.clk_i(clk_i), .reset_i(reset_i), .*);

module arbiter_sva(
  input logic clk_i, reset_i,

  // DUT ports (.* in bind will connect these)
  input  logic [63:0] idat_i, iadr_i, ddat_i, dadr_i, xdat_i,
  input  logic        iwe_i, icyc_i, istb_i, isigned_i,
  input  logic        dwe_i, dcyc_i, dstb_i, dsigned_i,
  input  logic [1:0]  isiz_i, dsiz_i,

  input  logic        xack_i,
  output logic [63:0] xdat_o, xadr_o, idat_o, ddat_o,
  output logic        xwe_o, xcyc_o, xstb_o, xsigned_o,
  output logic [1:0]  xsiz_o,
  output logic        iack_o, dack_o,

  // Internal DUT nets/regs
  input  logic        en_i, en_d,
  input  logic        reserve_i, reserve_d
);

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (reset_i);

  // Structural/arbiter core checks
  assert property ($onehot0({en_i,en_d}));
  assert property (en_i |-> icyc_i);
  assert property (en_d |-> dcyc_i);

  // Tie-break behavior when both request
  assert property (icyc_i && !dcyc_i |-> en_i && !en_d);
  assert property (!icyc_i && dcyc_i |-> en_d && !en_i);
  assert property (icyc_i && dcyc_i &&  reserve_i && !reserve_d |-> en_i && !en_d);
  assert property (icyc_i && dcyc_i && !reserve_i               |-> en_d && !en_i);

  // Reserve flops track previous grant; both cannot be 1
  assert property ($past(1'b1) |-> reserve_i == $past(en_i));
  assert property ($past(1'b1) |-> reserve_d == $past(en_d));
  assert property (!(reserve_i && reserve_d));

  // Output routing when I side is selected
  assert property (en_i |-> xdat_o==idat_i && xadr_o==iadr_i &&
                            xwe_o==iwe_i   && xcyc_o==icyc_i && xstb_o==istb_i &&
                            xsiz_o==isiz_i && xsigned_o==isigned_i &&
                            idat_o==xdat_i && ddat_o==64'd0);

  // Output routing when D side is selected
  assert property (en_d |-> xdat_o==ddat_i && xadr_o==dadr_i &&
                            xwe_o==dwe_i   && xcyc_o==dcyc_i && xstb_o==dstb_i &&
                            xsiz_o==dsiz_i && xsigned_o==dsigned_i &&
                            ddat_o==xdat_i && idat_o==64'd0);

  // Outputs idle when no grant
  assert property (!en_i && !en_d |-> xdat_o==64'd0 && xadr_o==64'd0 &&
                                     !xwe_o && !xcyc_o && !xstb_o &&
                                     xsiz_o==2'd0 && !xsigned_o &&
                                     idat_o==64'd0 && ddat_o==64'd0);

  // Ack routing and exclusivity
  assert property (iack_o == (en_i && xack_i));
  assert property (dack_o == (en_d && xack_i));
  assert property ($onehot0({iack_o,dack_o}));

  // No X on key outputs when active
  assert property (!$isunknown({xdat_o,xadr_o,xwe_o,xcyc_o,xstb_o,xsiz_o,xsigned_o,
                                iack_o,dack_o,idat_o,ddat_o}));

  // Reset-to-first tie case: both request right after reset -> D wins (due to reserves=0)
  assert property ($past(reset_i) && icyc_i && dcyc_i |-> en_d && !en_i);

  // Coverage
  cover property (icyc_i && !dcyc_i && en_i);
  cover property (!icyc_i && dcyc_i && en_d);
  cover property (icyc_i && dcyc_i && reserve_i && !reserve_d && en_i);
  cover property (icyc_i && dcyc_i && !reserve_i && en_d);
  cover property (en_i ##1 en_d);
  cover property (en_d ##1 en_i);
  cover property (!en_i && !en_d);

endmodule