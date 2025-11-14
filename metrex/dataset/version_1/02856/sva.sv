// SVA for openhmc_sync_fifo_reg_stage
// Bindable assertion module (concise, full functional checking + key coverage)
module openhmc_sync_fifo_reg_stage_sva #(parameter DWIDTH = 8)(
  input  logic                   clk,
  input  logic                   res_n,
  input  logic [DWIDTH-1:0]      d_in,
  input  logic [DWIDTH-1:0]      d_in_p,
  input  logic                   p_full,
  input  logic                   n_full,
  input  logic                   si,
  input  logic                   so,
  input  logic                   full,
  input  logic [DWIDTH-1:0]      d_out
);

  // Helpers (evaluate with previous full)
  let en_e     (pf) = (si & so & pf) | (si & ~so & ~pf & n_full) | (~si & so & p_full);
  let muxi_e   (pf) = (si & ~so) | (si & so & ~p_full & pf);
  let dsel_e   (pf) = muxi_e(pf) ? d_in : d_in_p;
  let full_ns  (pf) = (pf & si) | (pf & ~si & ~so) | (~si & so & p_full) | (si & ~so & n_full);

  // Async reset takes effect immediately
  property rst_async_zero;
    @(negedge res_n) 1'b1 |-> (full == 1'b0 && d_out == '0);
  endproperty
  assert property (rst_async_zero);

  // During reset low at clock edges, outputs are zero
  assert property (@(posedge clk) !res_n |-> (full == 1'b0 && d_out == '0));

  // No X on control/output when out of reset
  assert property (@(posedge clk) res_n |-> !$isunknown({si,so,p_full,n_full,full,d_out}));

  // Full next-state equation
  assert property (@(posedge clk) disable iff (!res_n || !$past(res_n))
                   full == full_ns($past(full)));

  // d_out update only when enabled, with correct source select
  assert property (@(posedge clk) disable iff (!res_n || !$past(res_n))
                   en_e($past(full)) |-> (d_out == dsel_e($past(full))));
  assert property (@(posedge clk) disable iff (!res_n || !$past(res_n))
                   !en_e($past(full)) |-> (d_out == $past(d_out)));

  // Explicit check for si&so case selects based on p_full
  assert property (@(posedge clk) disable iff (!res_n || !$past(res_n))
                   (si & so & $past(full)) |-> (d_out == (p_full ? d_in_p : d_in)));

  // Minimal functional coverage
  cover property (@(posedge clk) disable iff (!res_n)) (si & so & $past(full));                 // en term1
  cover property (@(posedge clk) disable iff (!res_n)) (si & ~so & ~$past(full) & n_full);      // en term2
  cover property (@(posedge clk) disable iff (!res_n)) (~si & so & p_full);                     // en term3
  cover property (@(posedge clk) disable iff (!res_n)) (si & ~so);                              // muxi branch A
  cover property (@(posedge clk) disable iff (!res_n)) (si & so & ~p_full & $past(full));       // muxi branch B
  cover property (@(posedge clk) disable iff (!res_n || !$past(res_n))) (!$past(full) && full); // 0->1
  cover property (@(posedge clk) disable iff (!res_n || !$past(res_n))) ($past(full) && !full); // 1->0

endmodule

// Bind into DUT
bind openhmc_sync_fifo_reg_stage
  openhmc_sync_fifo_reg_stage_sva #(.DWIDTH(DWIDTH)) openhmc_sync_fifo_reg_stage_sva_i (
    .clk   (clk),
    .res_n (res_n),
    .d_in  (d_in),
    .d_in_p(d_in_p),
    .p_full(p_full),
    .n_full(n_full),
    .si    (si),
    .so    (so),
    .full  (full),
    .d_out (d_out)
  );