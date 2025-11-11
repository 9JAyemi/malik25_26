// SVA checker for up_xfer_cntrl
// Bind this file to the DUT to verify CDC toggle/data transfer

module up_xfer_cntrl_sva #(
  parameter DATA_WIDTH = 8
)(
  input                   up_clk,
  input                   up_rstn,
  input                   d_clk,
  input                   d_rst,

  input  [DATA_WIDTH-1:0] up_data_cntrl,
  input  [DATA_WIDTH-1:0] d_data_cntrl,

  input                   up_xfer_done,
  input                   up_xfer_enable_s,

  input                   up_xfer_state_m1,
  input                   up_xfer_state_m2,
  input                   up_xfer_state,
  input        [5:0]      up_xfer_count,
  input                   up_xfer_toggle,
  input  [DATA_WIDTH-1:0] up_xfer_data,

  input                   d_xfer_toggle_m1,
  input                   d_xfer_toggle_m2,
  input                   d_xfer_toggle_m3,
  input                   d_xfer_toggle,
  input                   d_xfer_toggle_s
);

  // -------------------------------
  // Reset values
  // -------------------------------
  assert property (@(posedge up_clk) !up_rstn |-> (
      up_xfer_state_m1==0 && up_xfer_state_m2==0 && up_xfer_state==0 &&
      up_xfer_count==0 && up_xfer_done==0 && up_xfer_toggle==0 && up_xfer_data=='0
  ));

  assert property (@(posedge d_clk) d_rst |-> (
      d_xfer_toggle_m1==0 && d_xfer_toggle_m2==0 && d_xfer_toggle_m3==0 &&
      d_xfer_toggle==0 && d_data_cntrl=='0
  ));

  // -------------------------------
  // Source clock-domain checks
  // -------------------------------
  // Counter increments modulo 64
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_count == (($past(up_xfer_count)==6'd63) ? 6'd0 : $past(up_xfer_count)+6'd1)
  );

  // up_xfer_enable_s definition
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_enable_s == (up_xfer_state ^ up_xfer_toggle)
  );

  // Synchronizer pipeline in UP domain
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_state_m2 == $past(up_xfer_state_m1)
  );
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_state    == $past(up_xfer_state_m2)
  );

  // up_xfer_done matches its combinational condition and is 1-cycle pulse
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_done == ((up_xfer_count==6'd1) && (up_xfer_enable_s==1'b0))
  );
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_done |-> ##1 !up_xfer_done
  );

  // Toggle and data capture occur iff allowed window (count==1 and enable low)
  sequence src_fire;
    (up_xfer_count==6'd1) && (up_xfer_enable_s==1'b0);
  endsequence

  assert property (@(posedge up_clk) disable iff (!up_rstn)
    src_fire |-> (up_xfer_toggle != $past(up_xfer_toggle) && up_xfer_data == up_data_cntrl)
  );

  assert property (@(posedge up_clk) disable iff (!up_rstn)
    (up_xfer_toggle != $past(up_xfer_toggle)) |-> src_fire
  );

  assert property (@(posedge up_clk) disable iff (!up_rstn)
    (up_xfer_data != $past(up_xfer_data)) |-> src_fire
  );

  // No unknowns post-reset
  assert property (@(posedge up_clk) up_rstn |-> !$isunknown({up_xfer_done, up_xfer_toggle, up_xfer_enable_s}));

  // -------------------------------
  // Destination clock-domain checks
  // -------------------------------
  // Synchronizer pipeline in D domain
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_m2 == $past(d_xfer_toggle_m1)
  );
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_m3 == $past(d_xfer_toggle_m2)
  );
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle    == d_xfer_toggle_m3
  );

  // Pulse detect logic correctness
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_s == (d_xfer_toggle_m3 ^ d_xfer_toggle_m2)
  );

  // Toggle change iff pulse (same-cycle)
  assert property (@(posedge d_clk) disable iff (d_rst)
    (d_xfer_toggle != $past(d_xfer_toggle)) |-> d_xfer_toggle_s
  );
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_s |-> (d_xfer_toggle != $past(d_xfer_toggle))
  );

  // Data updates only on pulse and matches source-captured data
  assert property (@(posedge d_clk) disable iff (d_rst)
    (!d_xfer_toggle_s) |-> $stable(d_data_cntrl)
  );
  assert property (@(posedge d_clk) disable iff (d_rst)
    (d_data_cntrl != $past(d_data_cntrl)) |-> d_xfer_toggle_s
  );
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_s |-> (d_data_cntrl == up_xfer_data)
  );

  // No unknowns post-reset
  assert property (@(posedge d_clk) !d_rst |-> !$isunknown({d_xfer_toggle, d_xfer_toggle_s, d_data_cntrl}));

  // -------------------------------
  // Coverage
  // -------------------------------
  // One complete source-side fire
  cover property (@(posedge up_clk) disable iff (!up_rstn)
    src_fire and (up_xfer_toggle != $past(up_xfer_toggle))
  );

  // One complete destination receipt (data changes on pulse)
  cover property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_s and (d_data_cntrl != $past(d_data_cntrl))
  );

  // Two successive transfers with different data observed in dest domain
  cover property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_toggle_s ##[1:200] (d_xfer_toggle_s && (d_data_cntrl != $past(d_data_cntrl)))
  );

  // Exercise both polarities of the toggle in dest domain
  cover property (@(posedge d_clk) disable iff (d_rst) $rose(d_xfer_toggle));
  cover property (@(posedge d_clk) disable iff (d_rst) $fell(d_xfer_toggle));

endmodule

// Bind into the DUT
bind up_xfer_cntrl up_xfer_cntrl_sva #(.DATA_WIDTH(DATA_WIDTH)) u_up_xfer_cntrl_sva (
  .up_clk(up_clk),
  .up_rstn(up_rstn),
  .d_clk(d_clk),
  .d_rst(d_rst),

  .up_data_cntrl(up_data_cntrl),
  .d_data_cntrl(d_data_cntrl),

  .up_xfer_done(up_xfer_done),
  .up_xfer_enable_s(up_xfer_enable_s),

  .up_xfer_state_m1(up_xfer_state_m1),
  .up_xfer_state_m2(up_xfer_state_m2),
  .up_xfer_state(up_xfer_state),
  .up_xfer_count(up_xfer_count),
  .up_xfer_toggle(up_xfer_toggle),
  .up_xfer_data(up_xfer_data),

  .d_xfer_toggle_m1(d_xfer_toggle_m1),
  .d_xfer_toggle_m2(d_xfer_toggle_m2),
  .d_xfer_toggle_m3(d_xfer_toggle_m3),
  .d_xfer_toggle(d_xfer_toggle),
  .d_xfer_toggle_s(d_xfer_toggle_s)
);