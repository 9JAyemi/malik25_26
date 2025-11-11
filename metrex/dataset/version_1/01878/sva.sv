// SVA for prbs_gen and prbs_lfsr_tx
// Concise but high-quality checks and coverage

// Bind into prbs_lfsr_tx: check core LFSR behavior and I/O timing
module prbs_lfsr_tx_sva;
  // We are bound into prbs_lfsr_tx scope; direct names are visible
  default clocking cb @(posedge ck); endclocking

  // Basic protocol: o_vld is 1-cycle delayed i_req
  assert property (i_req |=> o_vld);
  assert property (!i_req |=> !o_vld);

  // o_res is 1-cycle delayed copy of r_lfsr[31]
  assert property (r_lfsr[31] |=> o_res);
  assert property (!r_lfsr[31] |=> !o_res);

  // Initialization takes precedence and loads seed
  assert property (i_init |=> (r_lfsr == $past(i_seed)));

  // Shift when requested by i_req or i_init_clk, unless init is occurring
  assert property ( ( (i_req || i_init_clk) && !i_init )
                   |=> r_lfsr == { $past(r_lfsr[30:0]),
                                   $past(r_lfsr[31] ^ r_lfsr[21] ^ r_lfsr[1] ^ r_lfsr[0]) } );

  // Hold when no shift/init request
  assert property ( !(i_req || i_init_clk) |=> (r_lfsr == $past(r_lfsr)) );

  // i_init implies i_init_clk same cycle (init pulses only during init clocking)
  assert property ( i_init |-> i_init_clk );

  // Coverage: see at least one init pulse and at least one post-init shift from i_req
  cover property ( i_init );
  cover property ( !i_init_clk ##1 !i_init_clk ##1 i_req ##1 o_vld );
endmodule
bind prbs_lfsr_tx prbs_lfsr_tx_sva();

// Bind into prbs_gen: check init sequencing, mapping, and top-level protocol
module prbs_gen_sva;
  // We are bound into prbs_gen scope; direct names are visible
  default clocking cb @(posedge ck); endclocking

  // Aggregate per-lane init_vld and outputs for compact checks
  wire [127:0] init_vld_vec;
  wire [127:0] lane_vld_vec;
  wire [127:0] lane_res_vec;

  genvar gi;
  generate
    for (gi=0; gi<128; gi=gi+1) begin : sva_vecs
      assign init_vld_vec[gi] = g0[gi].init_vld;
      assign lane_vld_vec[gi] = g0[gi].prbs_lfsr_tx.o_vld;
      assign lane_res_vec[gi] = g0[gi].prbs_lfsr_tx.o_res;
      // Each lane must be initialized at most once
      assert property ( $rose(init_vld_vec[gi]) |-> not ##[1:$] $rose(init_vld_vec[gi]) );
      // Top o_vld equals every lane's o_vld (all lanes share i_req timing)
      assert property ( o_vld == lane_vld_vec[gi] );
      // Top o_res mapping equals per-lane o_res
      assert property ( {o_res_upper,o_res_lower}[gi] == lane_res_vec[gi] );
    end
  endgenerate

  // During init clocking, exactly one lane gets init_vld; otherwise, none
  // Use $onehot for exactly-one when init clocking is active
  wire init_clk = g0[0].prbs_lfsr_tx.i_init_clk;
  assert property ( init_clk |-> $onehot(init_vld_vec) );
  assert property ( !init_clk |-> (init_vld_vec == '0) );

  // o_vld is 1-cycle delayed i_req at top level
  assert property ( i_req |=> o_vld );
  assert property ( !i_req |=> !o_vld );

  // While not shifting (no init clock and no i_req), output data bus is stable next cycle
  assert property ( (!init_clk && !i_req) |=> $stable({o_res_upper,o_res_lower}) );

  // Ready behavior:
  // - Stays low for 128 cycles after reset deassert, then asserts and sticks high
  // - When ready is high, init clock must be low
  assert property ( $fell(rst) |-> (!o_rdy[*128] ##1 o_rdy) );
  assert property ( o_rdy |=> o_rdy );
  assert property ( o_rdy |-> !init_clk );

  // Outputs not X when valid
  assert property ( o_vld |-> !$isunknown({o_res_upper,o_res_lower}) );

  // Coverage:
  // - See full init window (start and completion)
  // - See at least two valid beats after ready
  cover property ( $fell(rst) ##[1:200] o_rdy );
  cover property ( o_rdy ##1 i_req ##1 o_vld ##1 i_req ##1 o_vld );
  // - Observe first and last lane initialization occurred
  cover property ( init_clk and init_vld_vec[0] ##[1:200] init_clk and init_vld_vec[127] );
endmodule
bind prbs_gen prbs_gen_sva();