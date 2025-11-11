// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        up_down,
  input logic        load,
  input logic [2:0]  D,
  input logic [2:0]  Q
);

  // track first sampled cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // sanity: inputs known at sampling
  a_inputs_known: assert property (@(posedge clk) !$isunknown({load, up_down, D}));

  // next-state function (matches RTL semantics: load > hold > inc; no dec path exists)
  function automatic logic [2:0] f_next(logic [2:0] q, logic ld, logic [2:0] d, logic ud);
    f_next = ld ? d : (ud ? (q + 3'd1) : q);
  endfunction

  // single golden next-state check
  a_next_state: assert property (
    @(posedge clk) disable iff (!past_valid)
      Q == f_next($past(Q), $past(load), $past(D), $past(up_down))
  );

  // never decrement (dead else branch in RTL)
  a_no_dec: assert property (
    @(posedge clk) disable iff (!past_valid)
      !$past(load) |-> Q != ($past(Q) - 3'd1)
  );

  // explicit wrap-around on increment
  a_wrap: assert property (
    @(posedge clk) disable iff (!past_valid)
      $past(!load && up_down && Q==3'd7) |-> Q==3'd0
  );

  // concise functional coverage
  c_load:        cover property (@(posedge clk) disable iff (!past_valid) $past(load) && Q==$past(D));
  c_hold:        cover property (@(posedge clk) disable iff (!past_valid) $past(!load && !up_down) && Q==$past(Q));
  c_inc:         cover property (@(posedge clk) disable iff (!past_valid) $past(!load && up_down) && Q==($past(Q)+3'd1));
  c_wrap:        cover property (@(posedge clk) disable iff (!past_valid) $past(!load && up_down && Q==3'd7) && Q==3'd0);
  c_load_prio:   cover property (@(posedge clk) disable iff (!past_valid) $past(load && up_down) && Q==$past(D));

endmodule

// bind into DUT
bind up_down_counter up_down_counter_sva sva (
  .clk(clk),
  .up_down(up_down),
  .load(load),
  .D(D),
  .Q(Q)
);