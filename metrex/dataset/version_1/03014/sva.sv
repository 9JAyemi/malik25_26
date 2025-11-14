// SVA for tx_data_send
module tx_data_send_sva(
  input logic        pclk_tx,
  input logic        enable_tx,
  input logic        send_null_tx,
  input logic        get_data,
  input logic        get_data_0,
  input logic [7:0]  timecode_tx_i,
  input logic        tickin_tx,
  input logic [8:0]  data_tx_i,
  input logic        txwrite_tx,
  input logic        fct_counter_p,

  input logic [8:0]  tx_data_in,
  input logic [8:0]  tx_data_in_0,
  input logic        process_data,
  input logic        process_data_0,
  input logic [7:0]  tx_tcode_in,
  input logic        tcode_rdy_trnsp,

  // internal wire from DUT (bind to it)
  input logic        process_data_en
);
  default clocking cb @(posedge pclk_tx); endclocking
  default disable iff (!enable_tx);

  let p_en = txwrite_tx && fct_counter_p;

  // Asynchronous reset values held while enable_tx==0
  assert property (@(posedge pclk_tx) disable iff (1'b0)
                   !enable_tx |-> (process_data==0 && process_data_0==0 &&
                                   tcode_rdy_trnsp==0 &&
                                   tx_data_in==9'd0 && tx_data_in_0==9'd0 &&
                                   tx_tcode_in==8'd0));

  // Internal combinational definition
  assert property (process_data_en == (txwrite_tx && fct_counter_p));

  // When not sending, all outputs hold
  assert property (!send_null_tx |=> $stable({process_data,process_data_0,
                                              tcode_rdy_trnsp,tx_data_in,
                                              tx_data_in_0,tx_tcode_in}));

  // Timecode/tcode_rdy updates under send_null_tx
  assert property (send_null_tx && tickin_tx
                   |=> (tx_tcode_in==$past(timecode_tx_i) && tcode_rdy_trnsp));
  assert property (send_null_tx && !tickin_tx
                   |=> (!tcode_rdy_trnsp && $stable(tx_tcode_in)));

  // !txwrite clears data process flags
  assert property (send_null_tx && !txwrite_tx
                   |=> (!process_data && !process_data_0));

  // Data path: get_data has priority
  assert property (send_null_tx && p_en && get_data
                   |=> (process_data && !process_data_0 &&
                        tx_data_in==$past(data_tx_i)));
  // Data path: get_data_0 only
  assert property (send_null_tx && p_en && !get_data && get_data_0
                   |=> (!process_data && process_data_0 &&
                        tx_data_in_0==$past(data_tx_i)));
  // Both requests: get_data wins, tx_data_in_0 holds
  assert property (send_null_tx && p_en && get_data && get_data_0
                   |=> (process_data && !process_data_0 &&
                        tx_data_in==$past(data_tx_i) &&
                        $stable(tx_data_in_0)));

  // Else branch: hold data regs/flags when no qualifying request
  assert property (send_null_tx && txwrite_tx &&
                   !(get_data  && p_en) &&
                   !(get_data_0&& p_en)
                   |=> $stable({process_data,process_data_0,
                                tx_data_in,tx_data_in_0}));

  // One-hot (or zero) for process flags
  assert property (!(process_data && process_data_0));

  // Causality: flag rises imply proper enabling conditions
  assert property ($rose(process_data)
                   |-> $past(send_null_tx && p_en && get_data));
  assert property ($rose(process_data_0)
                   |-> $past(send_null_tx && p_en && !get_data && get_data_0));

  // Causality: tcode_rdy_trnsp rises only due to tickin under send_null
  assert property ($rose(tcode_rdy_trnsp)
                   |-> $past(send_null_tx && tickin_tx));

  // Known-value check when enabled
  assert property (! $isunknown({process_data,process_data_0,
                                 tcode_rdy_trnsp,tx_data_in,tx_data_in_0,
                                 tx_tcode_in}));

  // Coverage
  cover property (send_null_tx && tickin_tx |=> tcode_rdy_trnsp);
  cover property (send_null_tx && p_en && get_data
                  |=> process_data && tx_data_in==$past(data_tx_i));
  cover property (send_null_tx && p_en && !get_data && get_data_0
                  |=> process_data_0 && tx_data_in_0==$past(data_tx_i));
  cover property (send_null_tx && p_en && get_data && get_data_0
                  |=> process_data && !process_data_0);
  cover property (send_null_tx && !txwrite_tx |=> !process_data && !process_data_0);
  cover property (send_null_tx && txwrite_tx && !fct_counter_p &&
                  (get_data || get_data_0)
                  |=> $stable({process_data,process_data_0,tx_data_in,tx_data_in_0}));
endmodule

// Bind into DUT
bind tx_data_send tx_data_send_sva sva_tx_data_send(
  .pclk_tx(pclk_tx),
  .enable_tx(enable_tx),
  .send_null_tx(send_null_tx),
  .get_data(get_data),
  .get_data_0(get_data_0),
  .timecode_tx_i(timecode_tx_i),
  .tickin_tx(tickin_tx),
  .data_tx_i(data_tx_i),
  .txwrite_tx(txwrite_tx),
  .fct_counter_p(fct_counter_p),
  .tx_data_in(tx_data_in),
  .tx_data_in_0(tx_data_in_0),
  .process_data(process_data),
  .process_data_0(process_data_0),
  .tx_tcode_in(tx_tcode_in),
  .tcode_rdy_trnsp(tcode_rdy_trnsp),
  .process_data_en(process_data_en)
);