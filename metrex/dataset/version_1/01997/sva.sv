// SVA for up_xfer_status
module up_xfer_status_sva;

  localparam int DW = DATA_WIDTH-1;

  // d_clk domain: pipeline relations
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_state_m2 == $past(d_xfer_state_m1));
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_state == $past(d_xfer_state_m2));

  // d_clk domain: counter increments modulo-64
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_count == $past(d_xfer_count) + 6'd1);

  // d_clk domain: toggle only when allowed and must toggle when allowed
  assert property (@(posedge d_clk) disable iff (d_rst)
    $changed(d_xfer_toggle) |-> (d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0));
  assert property (@(posedge d_clk) disable iff (d_rst)
    ((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) |=> $changed(d_xfer_toggle));

  // d_clk domain: data handoff and accumulator behavior
  assert property (@(posedge d_clk) disable iff (d_rst)
    ((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) |=> (d_xfer_data == $past(d_acc_data)));
  assert property (@(posedge d_clk) disable iff (d_rst)
    !((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) |=> $stable(d_xfer_data));
  assert property (@(posedge d_clk) disable iff (d_rst)
    ((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) |=> (d_acc_data == d_data_status));
  assert property (@(posedge d_clk) disable iff (d_rst)
    !((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) |=> (d_acc_data == ($past(d_acc_data) | d_data_status)));

  // d_clk domain: stability while busy
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_enable_s |-> $stable(d_xfer_data));
  assert property (@(posedge d_clk) disable iff (d_rst)
    d_xfer_enable_s |-> !$changed(d_xfer_toggle));

  // up_clk domain: pipeline relations
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_toggle_m2 == $past(up_xfer_toggle_m1));
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_toggle_m3 == $past(up_xfer_toggle_m2));
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_toggle == $past(up_xfer_toggle_m3));

  // up_clk domain: single-cycle pulse and data gating
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_toggle_s |-> ##1 !up_xfer_toggle_s);
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    $changed(up_data_status) |-> up_xfer_toggle_s);
  assert property (@(posedge up_clk) disable iff (!up_rstn)
    !up_xfer_toggle_s |-> $stable(up_data_status));

  // Cross-domain liveness: d_toggle -> up pulse within bounded latency
  property d2u_pulse_liveness;
    @(posedge d_clk) disable iff (d_rst || !up_rstn)
      $changed(d_xfer_toggle) |-> @(posedge up_clk) ##[1:8] up_xfer_toggle_s;
  endproperty
  assert property (d2u_pulse_liveness);

  // Cross-domain liveness: up pulse -> d ack (enable clears) within bound
  property u2d_ack_liveness;
    @(posedge up_clk) disable iff (d_rst || !up_rstn)
      up_xfer_toggle_s |-> @(posedge d_clk) ##[1:8] (d_xfer_state == d_xfer_toggle);
  endproperty
  assert property (u2d_ack_liveness);

  // Cross-domain data integrity: value captured in d domain is seen in up domain
  property data_integrity;
    logic [DW:0] v;
    @(posedge d_clk) disable iff (d_rst || !up_rstn)
      ($changed(d_xfer_toggle), v = d_xfer_data)
        |-> @(posedge up_clk) ##[1:8] (up_xfer_toggle_s && (up_data_status == v));
  endproperty
  assert property (data_integrity);

  // Reset values
  assert property (@(posedge d_clk)
    d_rst |-> (d_xfer_state_m1==0 && d_xfer_state_m2==0 && d_xfer_state==0 &&
               d_xfer_count==0 && d_xfer_toggle==0 && d_xfer_data=='0 && d_acc_data=='0));
  assert property (@(posedge up_clk)
    !up_rstn |-> (up_xfer_toggle_m1==0 && up_xfer_toggle_m2==0 && up_xfer_toggle_m3==0 &&
                  up_xfer_toggle==0 && up_data_status=='0));

  // Coverage
  cover property (@(posedge d_clk) disable iff (d_rst || !up_rstn)
    !((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) [*2] ##1
    ((d_xfer_count == 6'd1) && (d_xfer_enable_s == 1'b0)) ##1 $changed(d_xfer_toggle));
  cover property (@(posedge up_clk) disable iff (!up_rstn)
    up_xfer_toggle_s ##[1:32] up_xfer_toggle_s);
  cover property (@(posedge up_clk) disable iff (!up_rstn)
    $changed(up_data_status));

endmodule

bind up_xfer_status up_xfer_status_sva up_xfer_status_sva_i();