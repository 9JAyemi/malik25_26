// SVA checker for decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_blk_mem_gen_v8_3_4
// Focus: data integrity, read-after-write semantics, stability, basic coverage

module blk_mem_gen_v8_3_4_sva
(
  input logic                 clk,
  input logic                 tmp_ram_rd_en,   // write when 0
  input logic [7:0]           Q,               // write addr
  input logic [0:0]           out,             // read addr (1-bit => addr 0/1)
  input logic [63:0]          din,
  input logic [63:0]          dout,
  input logic [0:0]           E,
  input logic [7:0]           gc0_count
);

  // lightweight reference model for assertions
  bit past_valid;
  bit                vld [256];
  logic [63:0]       ref [256];

  // Update reference model on writes (write when tmp_ram_rd_en==0)
  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (!tmp_ram_rd_en) begin
      ref[Q] = din;     // blocking to ensure assertion sees same-cycle update
      vld[Q] = 1'b1;
    end
  end

  // Read must return reference value for valid locations
  property p_read_matches_ref;
    @(posedge clk) past_valid && vld[out] |-> (dout == ref[out]);
  endproperty
  assert property (p_read_matches_ref);

  // Read-after-write, next-cycle to same address must see last written data
  property p_raw_next_cycle;
    @(posedge clk)
      past_valid && $past(!tmp_ram_rd_en) && (out == $past(Q))
      |-> (dout == $past(din));
  endproperty
  assert property (p_raw_next_cycle);

  // If read address is stable and no write to that address, dout must be stable
  property p_hold_when_no_write;
    @(posedge clk)
      past_valid && $stable(out) && !(!tmp_ram_rd_en && (Q == out))
      |-> $stable(dout);
  endproperty
  assert property (p_hold_when_no_write);

  // No X/Z on dout when reading a validized location
  property p_no_x_on_valid_read;
    @(posedge clk) past_valid && vld[out] |-> !$isunknown(dout);
  endproperty
  assert property (p_no_x_on_valid_read);

  // Sanity: read address is within implemented range (trivial here: 0/1)
  assert property (@(posedge clk) out inside {1'b0,1'b1});

  // --------------- Coverage ---------------

  // See both write-enable states
  cover property (@(posedge clk) !tmp_ram_rd_en);
  cover property (@(posedge clk)  tmp_ram_rd_en);

  // Exercise both readable addresses
  cover property (@(posedge clk) out==1'b0);
  cover property (@(posedge clk) out==1'b1);

  // Read-after-write to same address within 1 cycle
  cover property (@(posedge clk) !tmp_ram_rd_en ##1 (out==$past(Q)));

  // Back-to-back writes to same address
  cover property (@(posedge clk) !tmp_ram_rd_en ##1 (!tmp_ram_rd_en && (Q==$past(Q))));

  // Same-cycle write to currently read address
  cover property (@(posedge clk) !tmp_ram_rd_en && (Q==out));

  // Stimulus touches otherwise-unused controls
  cover property (@(posedge clk) $changed(E));
  cover property (@(posedge clk) $changed(gc0_count));

endmodule

// Bind into DUT (adjust instance name/scope as needed)
bind decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_blk_mem_gen_v8_3_4
  blk_mem_gen_v8_3_4_sva
  sva_i (
    .clk(clk),
    .tmp_ram_rd_en(tmp_ram_rd_en),
    .Q(Q),
    .out(out),
    .din(din),
    .dout(dout),
    .E(E),
    .gc0_count(\gc0.count_d1_reg[7] )
  );