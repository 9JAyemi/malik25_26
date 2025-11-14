// SVA for bt_transmitter
module bt_transmitter_sva #(parameter int n=8, m=8, int baud_rate=9600);
  localparam int RELOAD = (50_000_000/baud_rate)-1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  bit past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Counter range
  ap_cnt_range:      assert property (counter >= 0 && counter <= RELOAD);

  // Counter behavior
  ap_cnt_dec:        assert property (past_valid && counter > 0 |=> counter == $past(counter)-1);
  ap_cnt_reload:     assert property (past_valid && counter == 0 |=> counter == RELOAD);

  // Outputs only change on update (counter==0)
  ap_stable_count:   assert property (counter > 0 |-> $stable(tx_out) && $stable(tx_en));

  // Update semantics on counter==0
  ap_en_on_zero:     assert property (past_valid && counter == 0 |=> tx_en == 1'b1);
  ap_tx_from_dr:     assert property (past_valid && counter == 0 |=> tx_out == $past(data_reg));
  ap_dr_shift:       assert property (past_valid && counter == 0 |=> data_reg == ($past(data_reg) >> 1));

  // No unknowns on outputs when active
  ap_no_x:           assert property (!$isunknown({tx_en, tx_out}));

  // Async reset drives known reset values by next clk
  ap_reset_vals:     assert property (@(posedge clk) disable iff(1'b0) $rose(reset) |-> (counter==0 && tx_en==0 && tx_out=={m{1'b0}}));

  // Progress: see a zero within RELOAD cycles
  ap_progress:       assert property (past_valid |-> ##[0:RELOAD] (counter==0));

  // Coverage
  cv_first_enable:   cover property (past_valid && $rose(tx_en));
  cv_two_updates:    cover property (counter==0 ##[1:RELOAD] counter==0);
  cv_tx_change:      cover property (past_valid && counter==0 ##1 (tx_out != $past(tx_out)));
endmodule

bind bt_transmitter bt_transmitter_sva #(.n(n), .m(m), .baud_rate(baud_rate)) bt_transmitter_sva_i();


// SVA for bt_receiver
module bt_receiver_sva #(parameter int n=8, m=8, int baud_rate=9600);
  localparam int RELOAD = (50_000_000/baud_rate)-1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  bit past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Counter range
  ap_cnt_range:      assert property (counter >= 0 && counter <= RELOAD);

  // Counter behavior
  ap_cnt_dec:        assert property (past_valid && counter > 0 |=> counter == $past(counter)-1);
  ap_cnt_reload:     assert property (past_valid && counter == 0 |=> counter == RELOAD);

  // Outputs only change on update (counter==0)
  ap_stable_count:   assert property (counter > 0 |-> $stable(data_out) && $stable(rx_en));

  // Update semantics on counter==0
  ap_en_on_zero:     assert property (past_valid && counter == 0 |=> rx_en == 1'b1);
  ap_do_from_dr:     assert property (past_valid && counter == 0 |=> data_out == $past(data_reg));
  ap_dr_shift:       assert property (past_valid && counter == 0 |=> data_reg == ($past(data_reg) >> 1));

  // No unknowns on outputs when active
  ap_no_x:           assert property (!$isunknown({rx_en, data_out}));

  // Async reset drives known reset values by next clk
  ap_reset_vals:     assert property (@(posedge clk) disable iff(1'b0) $rose(reset) |-> (counter==0 && rx_en==0 && data_out=={m{1'b0}}));

  // Progress: see a zero within RELOAD cycles
  ap_progress:       assert property (past_valid |-> ##[0:RELOAD] (counter==0));

  // Coverage
  cv_first_enable:   cover property (past_valid && $rose(rx_en));
  cv_two_updates:    cover property (counter==0 ##[1:RELOAD] counter==0);
  cv_do_change:      cover property (past_valid && counter==0 ##1 (data_out != $past(data_out)));
endmodule

bind bt_receiver bt_receiver_sva #(.n(n), .m(m), .baud_rate(baud_rate)) bt_receiver_sva_i();