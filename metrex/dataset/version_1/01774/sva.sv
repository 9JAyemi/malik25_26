// SVA for spi_amba_connector
// Bind into DUT; directly references DUT internals.
module spi_amba_connector_sva;

  // Default clock and reset
  default clocking cb @ (posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity/X checks (after reset released)
  assert property (!$isunknown({phase, spi_ready_send, spi_busy, hsel, hwrite}));

  // Synchronous reset effects (checked with explicit antecedent)
  assert property (@(posedge clk) rst |=> (spi_data_in == 8'h00 && spi_ready_send == 1'b0 && phase == 1'b0));

  // HRDATA mapping/encoding
  assert property (hrdata[7:0]  == (spi_busy ? spi_data_out_reg : spi_data_out));
  assert property (hrdata[8]    == (phase || spi_busy || spi_ready_send));
  assert property (hrdata[31:9] == '0);

  // Phase: enable only via valid write when idle and SPI not busy
  assert property ($rose(phase)
                   |-> (!spi_ready_send && !spi_busy && hsel && hwrite && (haddr[15:0] == 16'h0000)));
  assert property ((!spi_ready_send && !spi_busy && !phase && hsel && hwrite && (haddr[15:0] == 16'h0000))
                   |=> phase);

  // Phase clear only when interface idle; same cycle raises ready
  assert property ($fell(phase) |-> (!spi_ready_send && !spi_busy));
  assert property ($fell(phase) |-> $rose(spi_ready_send));
  assert property (phase && !spi_ready_send && !spi_busy |=> (!phase && $rose(spi_ready_send)));

  // Ready-send: can only rise when phase was set and SPI not busy; falls only when busy
  assert property ($rose(spi_ready_send) |-> (!spi_busy && $past(phase)));
  assert property ($fell(spi_ready_send) |-> spi_busy);
  assert property (spi_ready_send && spi_busy |=> !spi_ready_send);

  // Data moves on phase completion (NB-assigns observed next posedge)
  assert property ($fell(phase) |=> (spi_data_in      == $past(spi_data_in_reg)));
  assert property ($fell(phase) |=> (spi_data_out_reg == $past(spi_data_in)));

  // Track hwdata captured at negedge during phase and check it is presented on spi_data_in
  logic [7:0] last_hw;
  always @(negedge clk or posedge rst) begin
    if (rst) last_hw <= '0;
    else if (phase) last_hw <= hwdata[7:0];
  end
  assert property ($fell(phase) |=> (spi_data_in == last_hw));

  // Coverage: full transaction from write -> phase -> ready -> busy handshake
  cover property (
    !phase && !spi_busy && !spi_ready_send
    ##1 (hsel && hwrite && (haddr[15:0] == 16'h0000))
    ##1 phase
    ##1 (phase && !spi_busy && !spi_ready_send)
    ##1 (!phase && spi_ready_send)
    ##[1:10] spi_busy
    ##1 !spi_ready_send
  );

  // Coverage: hrdata[8] asserted by each contributing source
  cover property (phase && !spi_busy && !spi_ready_send ##1 hrdata[8]);
  cover property (!phase &&  spi_busy && !spi_ready_send ##1 hrdata[8]);
  cover property (!phase && !spi_busy &&  spi_ready_send ##1 hrdata[8]);

endmodule

bind spi_amba_connector spi_amba_connector_sva sva_inst();