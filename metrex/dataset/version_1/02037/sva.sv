// SVA for altera_up_av_config_auto_init_ltm
// Bind this module to the DUT
bind altera_up_av_config_auto_init_ltm altera_up_av_config_auto_init_ltm_sva();

module altera_up_av_config_auto_init_ltm_sva;

  // Past-valid guard
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // Constants table for per-state expected rom_data
  localparam int NSTATE = 20;

  // 6-bit field used for rom_data[15:10]
  localparam logic [5:0] SIX [0:NSTATE-1] = '{
    6'h02, 6'h03, 6'h04, 6'h11, 6'h12, 6'h13, 6'h14, 6'h15, 6'h16, 6'h17,
    6'h18, 6'h19, 6'h1A, 6'h1B, 6'h1C, 6'h1D, 6'h1E, 6'h1F, 6'h20, 6'h21
  };

  // 8-bit field used for rom_data[7:0]
  localparam logic [7:0] BYTE [0:NSTATE-1] = '{
    8'h07, 8'hDF, 8'h17, 8'h00, 8'h5B, 8'hFF, 8'h00, 8'h20, 8'h40, 8'h80,
    8'h00, 8'h80, 8'h00, 8'h00, 8'h80, 8'hC0, 8'hE0, 8'hFF, 8'hD2, 8'hD2
  };

  // Basic sanity on rom_data formatting
  assert property (@(posedge clk) rom_data[23:16] == 8'h00);
  assert property (@(posedge clk) rom_data[9:8]   == 2'b00);

  // State stays in legal range after the first cycle
  assert property (@(posedge clk) past_valid |-> (state_reg inside {[5'd0:5'd19]}));

  // Any illegal previous state drives next state to STATE_0
  assert property (@(posedge clk) past_valid && !($past(state_reg) inside {[5'd0:5'd19]}) |-> state_reg == 5'd0);

  // No skipped transitions when previous state was legal
  assert property (@(posedge clk)
    past_valid && ($past(state_reg) inside {[5'd0:5'd19]})
    |-> (state_reg == $past(state_reg)) ||
        (state_reg == (($past(state_reg)==5'd19) ? 5'd0 : $past(state_reg)+5'd1))
  );

  // Per-state transition checks, per-state output checks, and coverage
  genvar i;
  generate
    for (i = 0; i < NSTATE; i++) begin : GEN_SVA
      localparam logic [4:0] SIDX  = i[4:0];
      localparam logic [4:0] NEXTI = (i==NSTATE-1) ? 5'd0 : (i+1)[4:0];

      // Stay when rom_address matches state
      assert property (@(posedge clk)
        past_valid && $past(state_reg) == SIDX && $past(rom_address) == SIDX
        |-> state_reg == SIDX
      );

      // Advance when rom_address mismatches state
      assert property (@(posedge clk)
        past_valid && $past(state_reg) == SIDX && $past(rom_address) != SIDX
        |-> state_reg == NEXTI
      );

      // Output content per state
      assert property (@(posedge clk)
        state_reg == SIDX |-> rom_data == {8'h00, SIX[i], 2'b00, BYTE[i]}
      );

      // Coverage: see each state
      cover property (@(posedge clk) state_reg == SIDX);

      // Coverage: see a stay transition
      cover property (@(posedge clk)
        state_reg == SIDX && rom_address == SIDX ##1 state_reg == SIDX
      );

      // Coverage: see an advance transition
      cover property (@(posedge clk)
        state_reg == SIDX && rom_address != SIDX ##1 state_reg == NEXTI
      );
    end
  endgenerate

  // Coverage: wrap-around from STATE_19 to STATE_0 on mismatch
  cover property (@(posedge clk)
    state_reg == 5'd19 && rom_address != 5'd19 ##1 state_reg == 5'd0
  );

endmodule