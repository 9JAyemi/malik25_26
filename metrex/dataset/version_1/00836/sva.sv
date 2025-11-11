// SVA for jt12_logsin
// Bind example:
// bind jt12_logsin jt12_logsin_sva u_jt12_logsin_sva(.clk(clk), .clk_en(clk_en), .addr(addr), .logsin(logsin));

module jt12_logsin_sva (
  input logic        clk,
  input logic        clk_en,
  input logic [7:0]  addr,
  input logic [11:0] logsin
);

  default clocking cb @(posedge clk); endclocking

  // Start guard for $past
  logic started, ce_seen;
  always_ff @(posedge clk) begin
    started <= 1'b1;
    if (clk_en) ce_seen <= 1'b1;
  end

  // Sanity: no X when used; and once initialized, output never X
  a_no_x_on_ce:          assert property (started && clk_en |-> (!$isunknown(addr) && !$isunknown(logsin)));
  a_no_x_after_first_ce: assert property (ce_seen |-> !$isunknown(logsin));

  // CE gating: output only changes when clk_en=1; when clk_en=0 output holds
  a_hold_no_ce:        assert property (started && !clk_en |-> $stable(logsin));
  a_change_implies_ce: assert property (started && $changed(logsin) |-> clk_en);

  // Determinism across successive captures
  a_same_addr_same_out: assert property (
    started && clk_en && $past(clk_en) && (addr == $past(addr)) |-> (logsin == $past(logsin))
  );

  // Monotonic ROM (non-decreasing with address)
  a_monotonic_up: assert property (
    started && clk_en && $past(clk_en) && (addr > $past(addr)) |-> (logsin >= $past(logsin))
  );
  a_monotonic_down: assert property (
    started && clk_en && $past(clk_en) && (addr < $past(addr)) |-> (logsin <= $past(logsin))
  );

  // Anchor value checks (concise but strong content integrity)
  a_zero_low_indices: assert property (started && clk_en && (addr inside {[8'd0:8'd7]})) |-> (logsin == 12'h000);
  a_anchor_128:       assert property (started && clk_en && (addr == 8'd128)) |-> (logsin == 12'h081);
  a_anchor_170:       assert property (started && clk_en && (addr == 8'd170)) |-> (logsin == 12'h0ff);
  a_anchor_255:       assert property (started && clk_en && (addr == 8'd255)) |-> (logsin == 12'h859);

  // Coverage
  covergroup cg_addr @(posedge clk);
    coverpoint addr iff (clk_en) { bins all[] = {[8'd0:8'd255]}; }
  endgroup
  cg_addr cg = new();

  cover property (clk_en);
  cover property (clk_en && (addr inside {[8'd0:8'd7]}) && (logsin == 12'h000));
  cover property (clk_en && addr == 8'd128 && logsin == 12'h081);
  cover property (clk_en && addr == 8'd170 && logsin == 12'h0ff);
  cover property (clk_en && addr == 8'd255 && logsin == 12'h859);
  cover property (clk_en && $past(clk_en) && (addr > $past(addr)) && (logsin >= $past(logsin)));
  cover property (!clk_en && $stable(logsin));

endmodule