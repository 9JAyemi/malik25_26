// SVA for hpdmc_mgmt
// Bind this file to the DUT
//   bind hpdmc_mgmt hpdmc_mgmt_sva #(.sdram_depth(sdram_depth),
//                                     .sdram_columndepth(sdram_columndepth),
//                                     .sdram_addrdepth(sdram_addrdepth)) u_sva (
//     .sys_clk(sys_clk), .sdram_rst(sdram_rst),
//     .tim_rp(tim_rp), .tim_rcd(tim_rcd), .tim_refi(tim_refi), .tim_rfc(tim_rfc),
//     .stb(stb), .we(we), .address(address), .ack(ack),
//     .read(read), .write(write), .concerned_bank(concerned_bank),
//     .read_safe(read_safe), .write_safe(write_safe), .precharge_safe(precharge_safe),
//     .sdram_cs(sdram_cs), .sdram_we(sdram_we), .sdram_cas(sdram_cas), .sdram_ras(sdram_ras),
//     .sdram_cs_n(sdram_cs_n), .sdram_we_n(sdram_we_n), .sdram_cas_n(sdram_cas_n), .sdram_ras_n(sdram_ras_n),
//     .sdram_adr(sdram_adr), .sdram_ba(sdram_ba),
//     .sdram_adr_loadrow(sdram_adr_loadrow), .sdram_adr_loadcol(sdram_adr_loadcol), .sdram_adr_loadA10(sdram_adr_loadA10),
//     .bank_address(bank_address), .bank_address_onehot(bank_address_onehot),
//     .row_address(row_address), .col_address(col_address),
//     .has_openrow(has_openrow), .openrows(openrows), .track_open(track_open), .track_close(track_close),
//     .current_precharge_safe(current_precharge_safe), .bank_open(bank_open), .page_hit(page_hit),
//     .precharge_counter(precharge_counter), .reload_precharge_counter(reload_precharge_counter), .precharge_done(precharge_done),
//     .activate_counter(activate_counter), .reload_activate_counter(reload_activate_counter), .activate_done(activate_done),
//     .refresh_counter(refresh_counter), .reload_refresh_counter(reload_refresh_counter), .must_refresh(must_refresh),
//     .autorefresh_counter(autorefresh_counter), .reload_autorefresh_counter(reload_autorefresh_counter), .autorefresh_done(autorefresh_done),
//     .state(state), .next_state(next_state)
//   );

module hpdmc_mgmt_sva #(
  parameter int sdram_depth = 26,
  parameter int sdram_columndepth = 9,
  parameter int sdram_addrdepth = sdram_depth-1-1-(sdram_columndepth+2)+1
)(
  input  logic                        sys_clk,
  input  logic                        sdram_rst,

  input  logic [2:0]                  tim_rp,
  input  logic [2:0]                  tim_rcd,
  input  logic [10:0]                 tim_refi,
  input  logic [3:0]                  tim_rfc,

  input  logic                        stb,
  input  logic                        we,
  input  logic [sdram_depth-2:0]      address,
  input  logic                        ack,

  input  logic                        read,
  input  logic                        write,
  input  logic [3:0]                  concerned_bank,
  input  logic                        read_safe,
  input  logic                        write_safe,
  input  logic [3:0]                  precharge_safe,

  input  logic                        sdram_cs,
  input  logic                        sdram_we,
  input  logic                        sdram_cas,
  input  logic                        sdram_ras,
  input  logic                        sdram_cs_n,
  input  logic                        sdram_we_n,
  input  logic                        sdram_cas_n,
  input  logic                        sdram_ras_n,
  input  logic [sdram_addrdepth-1:0]  sdram_adr,
  input  logic [1:0]                  sdram_ba,

  input  logic                        sdram_adr_loadrow,
  input  logic                        sdram_adr_loadcol,
  input  logic                        sdram_adr_loadA10,

  input  logic [1:0]                  bank_address,
  input  logic [3:0]                  bank_address_onehot,
  input  logic [sdram_addrdepth-1:0]  row_address,
  input  logic [sdram_columndepth-1:0] col_address,

  input  logic [3:0]                  has_openrow,
  input  logic [sdram_addrdepth-1:0]  openrows [0:3],
  input  logic [3:0]                  track_open,
  input  logic [3:0]                  track_close,

  input  logic                        current_precharge_safe,
  input  logic                        bank_open,
  input  logic                        page_hit,

  input  logic [2:0]                  precharge_counter,
  input  logic                        reload_precharge_counter,
  input  logic                        precharge_done,

  input  logic [2:0]                  activate_counter,
  input  logic                        reload_activate_counter,
  input  logic                        activate_done,

  input  logic [10:0]                 refresh_counter,
  input  logic                        reload_refresh_counter,
  input  logic                        must_refresh,

  input  logic [3:0]                  autorefresh_counter,
  input  logic                        reload_autorefresh_counter,
  input  logic                        autorefresh_done,

  input  logic [3:0]                  state,
  input  logic [3:0]                  next_state
);

  // Local command decodes (internal active-high command intent)
  wire rd_cmd  = sdram_cs && (sdram_ras==1'b0) && (sdram_cas==1'b1) && (sdram_we==1'b0);
  wire wr_cmd  = sdram_cs && (sdram_ras==1'b0) && (sdram_cas==1'b1) && (sdram_we==1'b1);
  wire act_cmd = sdram_cs && (sdram_ras==1'b1) && (sdram_cas==1'b0) && (sdram_we==1'b0);
  wire pre_cmd = sdram_cs && (sdram_ras==1'b1) && (sdram_cas==1'b0) && (sdram_we==1'b1);
  wire ref_cmd = sdram_cs && (sdram_ras==1'b1) && (sdram_cas==1'b1) && (sdram_we==1'b0);

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sdram_rst);

  // Basic structural checks
  assert property ($onehot(bank_address_onehot));
  assert property (concerned_bank == bank_address_onehot);
  assert property (sdram_ba == bank_address);
  assert property ($onehot0({sdram_adr_loadrow, sdram_adr_loadcol, sdram_adr_loadA10}));
  assert property ($onehot0({rd_cmd, wr_cmd, act_cmd, pre_cmd, ref_cmd}));

  // Active-low output mapping
  assert property (sdram_cs_n  == ~sdram_cs);
  assert property (sdram_we_n  == ~sdram_we);
  assert property (sdram_cas_n == ~sdram_cas);
  assert property (sdram_ras_n == ~sdram_ras);

  // Reset effects
  assert property (sdram_rst |=> state == 4'd0); // IDLE
  assert property (sdram_rst |=> has_openrow == 4'h0);
  assert property (sdram_rst |=> refresh_counter == 11'd0);

  // Handshake/command relationships
  assert property (!(read && write));
  assert property (read  |-> read_safe);
  assert property (write |-> write_safe);
  assert property (read  |-> rd_cmd && sdram_adr_loadcol);
  assert property (write |-> wr_cmd && sdram_adr_loadcol);
  assert property (ack   |-> (read ^ write));
  assert property (ack   |-> (rd_cmd || wr_cmd));
  assert property (ack   |-> next_state == 4'd0); // IDLE after issuing RD/WR

  // Command encodings vs address-load strobes
  assert property (rd_cmd  |-> sdram_adr_loadcol);
  assert property (wr_cmd  |-> sdram_adr_loadcol);
  assert property (act_cmd |-> sdram_adr_loadrow);
  assert property (sdram_adr_loadA10 |-> pre_cmd);
  assert property (sdram_adr_loadA10 |-> $onehot(sdram_adr) && sdram_adr[10]);

  // Address muxing correctness
  assert property (sdram_adr_loadrow |-> sdram_adr == row_address);
  assert property (sdram_adr_loadcol |-> sdram_adr[sdram_columndepth-1:0] == col_address);
  assert property (sdram_adr_loadcol |-> ~|sdram_adr[sdram_addrdepth-1:sdram_columndepth]);

  // Counter load/decrement behavior
  assert property (reload_precharge_counter |=> precharge_counter == $past(tim_rp));
  assert property (($past(!precharge_done) && !$past(reload_precharge_counter)) |-> precharge_counter == $past(precharge_counter) - 3'd1);

  assert property (reload_activate_counter |=> activate_counter == $past(tim_rcd));
  assert property (($past(!activate_done) && !$past(reload_activate_counter)) |-> activate_counter == $past(activate_counter) - 3'd1);

  assert property (reload_refresh_counter |=> refresh_counter == $past(tim_refi));
  assert property (($past(!must_refresh) && !$past(reload_refresh_counter)) |-> refresh_counter == $past(refresh_counter) - 11'd1);

  assert property (reload_autorefresh_counter |=> autorefresh_counter == $past(tim_rfc));
  assert property (($past(!autorefresh_done) && !$past(reload_autorefresh_counter)) |-> autorefresh_counter == $past(autorefresh_counter) - 4'd1);

  // State/transition/command relationships
  localparam logic [3:0] IDLE=4'd0, ACTIVATE=4'd1, READ=4'd2, WRITE=4'd3, PRECHARGEALL=4'd4, AUTOREFRESH=4'd5, AUTOREFRESH_WAIT=4'd6;

  // No command in IDLE when refreshing is pending; go to PRECHARGEALL
  assert property ((state==IDLE && must_refresh) |-> (!rd_cmd && !wr_cmd && !act_cmd && !pre_cmd && !ref_cmd) && next_state==PRECHARGEALL);

  // Page-hit immediate operations in IDLE
  assert property ((state==IDLE && stb && page_hit && !we && read_safe)  |-> rd_cmd && read  && ack && next_state==IDLE);
  assert property ((state==IDLE && stb && page_hit &&  we && write_safe) |-> wr_cmd && write && ack && next_state==IDLE);

  // Page-miss with bank open -> precharge that bank
  assert property ((state==IDLE && stb && !page_hit && bank_open && current_precharge_safe) |-> pre_cmd && reload_precharge_counter && (track_close==bank_address_onehot) && !sdram_adr_loadA10 && next_state==ACTIVATE);

  // Page-miss with bank closed -> activate selected row
  assert property ((state==IDLE && stb && !page_hit && !bank_open) |-> act_cmd && reload_activate_counter && (track_open==bank_address_onehot) && next_state inside {READ,WRITE});

  // ACTIVATE state: once precharge gap done, issue ACTIVATE
  assert property ((state==ACTIVATE && precharge_done) |-> act_cmd && sdram_adr_loadrow && reload_activate_counter && (track_open==bank_address_onehot));

  // READ/WRITE states: after tRCD and safe, issue column and return to IDLE
  assert property ((state==READ  && activate_done && read_safe)  |-> rd_cmd && read  && ack && next_state==IDLE);
  assert property ((state==WRITE && activate_done && write_safe) |-> wr_cmd && write && ack && next_state==IDLE);

  // PRECHARGEALL -> AUTOREFRESH
  assert property ((state==PRECHARGEALL && precharge_safe==4'b1111) |-> pre_cmd && sdram_adr_loadA10 && reload_precharge_counter && (track_close==4'hF) && next_state==AUTOREFRESH);

  // AUTOREFRESH issue
  assert property ((state==AUTOREFRESH && precharge_done) |-> ref_cmd && reload_refresh_counter && reload_autorefresh_counter && next_state==AUTOREFRESH_WAIT);

  // AUTOREFRESH_WAIT completion
  assert property ((state==AUTOREFRESH_WAIT && autorefresh_done) |-> next_state==IDLE);

  // Idle quiescence
  assert property ((state==IDLE && !stb && !must_refresh) |-> !rd_cmd && !wr_cmd && !act_cmd && !pre_cmd && !ref_cmd && !read && !write);

  // Tracking of open/closed rows
  // ACTIVATE sets has_openrow and captures row_address
  assert property ((act_cmd && (track_open!=4'b0)) |=> ( (has_openrow & $past(track_open)) == $past(track_open) ));
  assert property ((act_cmd && (track_open!=4'b0)) |=> openrows[$past(bank_address)] == $past(row_address));

  // PRECHARGE bank clears that bank, PRECHARGEALL clears all
  assert property ((pre_cmd && !sdram_adr_loadA10) |=> has_openrow[$past(bank_address)] == 1'b0);
  assert property ((pre_cmd &&  sdram_adr_loadA10) |=> has_openrow == 4'h0);

  // Page-hit / bank-open correctness
  assert property (bank_open == has_openrow[bank_address]);
  assert property (page_hit == (has_openrow[bank_address] && (openrows[bank_address] == row_address)));

  // Command implies proper counter reloads
  assert property (pre_cmd |-> reload_precharge_counter);
  assert property (act_cmd |-> reload_activate_counter);
  assert property (ref_cmd |-> (reload_refresh_counter && reload_autorefresh_counter));

  // Coverage
  cover property (state==IDLE && stb && !we && page_hit && read_safe ##1 rd_cmd && read && ack);
  cover property (state==IDLE && stb &&  we && page_hit && write_safe ##1 wr_cmd && write && ack);

  cover property (state==IDLE && stb && !we && !page_hit && bank_open && current_precharge_safe
                  ##1 pre_cmd ##[1:$] act_cmd ##[1:$] rd_cmd && ack);

  cover property (state==IDLE && stb &&  we && !page_hit && bank_open && current_precharge_safe
                  ##1 pre_cmd ##[1:$] act_cmd ##[1:$] wr_cmd && ack);

  cover property (state==IDLE && must_refresh
                  ##1 (state==PRECHARGEALL && pre_cmd && sdram_adr_loadA10)
                  ##[1:$] (state==AUTOREFRESH && ref_cmd)
                  ##[1:$] (state==AUTOREFRESH_WAIT && autorefresh_done)
                  ##1 state==IDLE);

endmodule