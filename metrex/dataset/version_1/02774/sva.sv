// SystemVerilog Assertions for agnus_audiodma
// Place inside the module or bind to agnus_audiodma

// Useful hpos slots
localparam logic [8:0] H0 = 9'b0001_0010_1;
localparam logic [8:0] H1 = 9'b0001_0100_1;
localparam logic [8:0] H2 = 9'b0001_0110_1;
localparam logic [8:0] H3 = 9'b0001_1000_1;

// Channel decode from hpos[3:2]
assert property (@(posedge clk) (hpos[3:2]==2'b01) |-> channel==2'd0);
assert property (@(posedge clk) (hpos[3:2]==2'b10) |-> channel==2'd1);
assert property (@(posedge clk) (hpos[3:2]==2'b11) |-> channel==2'd2);
assert property (@(posedge clk) (hpos[3:2]==2'b00) |-> channel==2'd3);

// DMA request/ack decode vs hpos
assert property (@(posedge clk) (hpos==H0) |-> (dmal==audio_dmal[0] && dmas==audio_dmas[0]));
assert property (@(posedge clk) (hpos==H1) |-> (dmal==audio_dmal[1] && dmas==audio_dmas[1]));
assert property (@(posedge clk) (hpos==H2) |-> (dmal==audio_dmal[2] && dmas==audio_dmas[2]));
assert property (@(posedge clk) (hpos==H3) |-> (dmal==audio_dmal[3] && dmas==audio_dmas[3]));
assert property (@(posedge clk) !(hpos inside {H0,H1,H2,H3}) |-> (dmal==1'b0 && dmas==1'b0));
assert property (@(posedge clk) dma==dmal);

// Address muxing
assert property (@(posedge clk) address_out[20:1]==audptout[20:1]);
assert property (@(posedge clk) audptout[20:1]==audpt[channel][20:1]);

// Register address select per channel
assert property (@(posedge clk) (channel==2'd0) |-> reg_address_out[8:1]==AUD0DAT_REG[8:1]);
assert property (@(posedge clk) (channel==2'd1) |-> reg_address_out[8:1]==AUD1DAT_REG[8:1]);
assert property (@(posedge clk) (channel==2'd2) |-> reg_address_out[8:1]==AUD2DAT_REG[8:1]);
assert property (@(posedge clk) (channel==2'd3) |-> reg_address_out[8:1]==AUD3DAT_REG[8:1]);

// LCH/LCL concatenation
assert property (@(posedge clk) audlcout[20:1]=={audlch[channel],audlcl[channel]});

// LCH/LCL writes when decoded
assert property (@(posedge clk) (clk7_en && audlcena && ~reg_address_in[1]) |=> audlch[audlcsel]==$past(data_in[4:0]));
assert property (@(posedge clk) (clk7_en && audlcena &&  reg_address_in[1]) |=> audlcl[audlcsel]==$past(data_in[15:1]));

// LCH/LCL hold when not written
genvar gi;
generate
  for (gi=0; gi<4; gi++) begin : g_lc_hold
    assert property (@(posedge clk) (clk7_en && !(audlcena && ~reg_address_in[1] && audlcsel==gi)) |=> audlch[gi]==$past(audlch[gi]));
    assert property (@(posedge clk) (clk7_en && !(audlcena &&  reg_address_in[1] && audlcsel==gi)) |=> audlcl[gi]==$past(audlcl[gi]));
  end
endgenerate

// Pointer update semantics
assert property (@(posedge clk) (clk7_en && dmal && dmas) |=> audpt[channel]==$past(audlcout[20:1]));
assert property (@(posedge clk) (clk7_en && dmal && !dmas)
                 |=> audpt[channel]==(($past({1'b0,audptout[20:1]})+21'd1)[20:1]));
// Non-selected channels hold on active cycles
generate
  for (gi=0; gi<4; gi++) begin : g_pt_hold
    assert property (@(posedge clk) (clk7_en && (channel!=gi)) |=> audpt[gi]==$past(audpt[gi]));
  end
endgenerate

// Simple X checking on key outputs
assert property (@(posedge clk) !$isunknown({dma,dmal,dmas}));
assert property (@(posedge clk) !$isunknown(address_out[20:1]));

// Functional coverage
generate
  for (gi=0; gi<4; gi++) begin : g_cov
    cover property (@(posedge clk) clk7_en && audlcena && ~reg_address_in[1] && audlcsel==gi);
    cover property (@(posedge clk) clk7_en && audlcena &&  reg_address_in[1] && audlcsel==gi);
    cover property (@(posedge clk) clk7_en && dmal && dmas && channel==gi);
    cover property (@(posedge clk) clk7_en && dmal && !dmas && channel==gi);
  end
endgenerate
cover property (@(posedge clk) (hpos inside {H0,H1,H2,H3}));