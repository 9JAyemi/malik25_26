// SVA for timer_wait
// Bind into DUT: bind timer_wait timer_wait_sva sva(.clk, .rsth, .mod_sel, .req, .w_wdata, .ack, .en_wait_countup, .en_wait_cnt, .wait_cnt, .req_1d, .req_pe);

module timer_wait_sva(
  input  logic        clk,
  input  logic        rsth,
  input  logic        mod_sel,
  input  logic        req,
  input  logic [7:0]  w_wdata,
  input  logic        ack,
  input  logic        en_wait_countup,
  input  logic [15:0] en_wait_cnt,
  input  logic [7:0]  wait_cnt,
  input  logic        req_1d,
  input  logic        req_pe
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior (check post-NBA using ##0)
  assert property (rsth |-> ##0 (req_1d==1'b0 && en_wait_cnt==16'd49999 && wait_cnt==8'd0));

  // Edge-detect pipeline
  assert property (disable iff (rsth) req_1d == $past(req));
  assert property (disable iff (rsth) req_pe == (mod_sel && req && !$past(req)));
  assert property (disable iff (rsth) req_pe |=> !req_pe); // 1-cycle pulse

  // Enable-tick generator correctness
  assert property (en_wait_countup == (en_wait_cnt==16'd0));
  assert property (disable iff (rsth) $past(en_wait_cnt)==16'd0 |-> en_wait_cnt==16'd49999);
  assert property (disable iff (rsth) ($past(en_wait_cnt)!=16'd0) |-> en_wait_cnt==$past(en_wait_cnt)-16'd1);
  assert property (disable iff (rsth) en_wait_countup |=> !en_wait_countup);
  assert property (disable iff (rsth) en_wait_countup |=> (!en_wait_countup[*49999] ##1 en_wait_countup));

  // wait_cnt next-state function
  assert property (disable iff (rsth)
    wait_cnt ==
      ( $past(req_pe)              ? $past(w_wdata) :
        ($past(wait_cnt)==8'd0)    ? $past(wait_cnt) :
        $past(en_wait_countup)     ? $past(wait_cnt)-8'd1 :
                                     $past(wait_cnt) ) );

  // ack correctness and immediate response on load
  assert property (ack == (wait_cnt==8'd0));
  assert property (disable iff (rsth) $past(req_pe) |-> (ack == ($past(w_wdata)==8'd0)));

  // Hold at zero unless reloaded
  assert property (disable iff (rsth) ($past(wait_cnt)==8'd0 && !$past(req_pe)) |-> wait_cnt==8'd0);

  // Coverage
  cover property (disable iff (rsth) req_pe && (w_wdata==8'd0) ##0 ack);
  cover property (disable iff (rsth) req_pe && (w_wdata!=8'd0) ##[1:$] ack);

endmodule

bind timer_wait timer_wait_sva sva(
  .clk(clk),
  .rsth(rsth),
  .mod_sel(mod_sel),
  .req(req),
  .w_wdata(w_wdata),
  .ack(ack),
  .en_wait_countup(en_wait_countup),
  .en_wait_cnt(en_wait_cnt),
  .wait_cnt(wait_cnt),
  .req_1d(req_1d),
  .req_pe(req_pe)
);