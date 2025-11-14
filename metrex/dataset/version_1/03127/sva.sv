// SVA checker for ad_axis_inf_rx
// Bind this file to the DUT: bind ad_axis_inf_rx ad_axis_inf_rx_sva #(.DATA_WIDTH(DATA_WIDTH)) i_ad_axis_inf_rx_sva(.*);

module ad_axis_inf_rx_sva #(parameter DATA_WIDTH=16)
(
  input clk, rst,
  // DUT I/O
  input valid, last,
  input [DATA_WIDTH-1:0] data,
  input inf_ready,
  input inf_valid, inf_last,
  input [DATA_WIDTH-1:0] inf_data,
  // DUT internals (bound by name)
  input [2:0] wcnt,
  input wlast_0, input [DATA_WIDTH-1:0] wdata_0,
  input wlast_1, input [DATA_WIDTH-1:0] wdata_1,
  input wlast_2, input [DATA_WIDTH-1:0] wdata_2,
  input wlast_3, input [DATA_WIDTH-1:0] wdata_3,
  input wlast_4, input [DATA_WIDTH-1:0] wdata_4,
  input wlast_5, input [DATA_WIDTH-1:0] wdata_5,
  input wlast_6, input [DATA_WIDTH-1:0] wdata_6,
  input wlast_7, input [DATA_WIDTH-1:0] wdata_7,
  input [2:0] rcnt,
  input inf_ready_s,
  input inf_last_s, input [DATA_WIDTH-1:0] inf_data_s
);

  localparam int DW = DATA_WIDTH-1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset effects (checked across the reset edge)
  property p_reset_state;
    @(posedge clk) rst |=> (wcnt==3'd0 && rcnt==3'd0 && !inf_valid && !inf_last && inf_data=='0);
  endproperty
  assert property (p_reset_state);

  // No X on key outputs/pointers after reset deasserted
  assert property (!$isunknown({wcnt, rcnt, inf_valid, inf_ready, inf_last, inf_data})));

  // Write counter behavior
  assert property ($past(valid) |-> (wcnt == $past(wcnt)+3'd1));
  assert property (!$past(valid) |-> (wcnt == $past(wcnt)));

  // Bank write on valid to selected index (1-cycle later)
  assert property ($past(valid && ($past(wcnt)==3'd0)) |-> (wlast_0==$past(last) && wdata_0==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd1)) |-> (wlast_1==$past(last) && wdata_1==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd2)) |-> (wlast_2==$past(last) && wdata_2==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd3)) |-> (wlast_3==$past(last) && wdata_3==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd4)) |-> (wlast_4==$past(last) && wdata_4==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd5)) |-> (wlast_5==$past(last) && wdata_5==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd6)) |-> (wlast_6==$past(last) && wdata_6==$past(data)));
  assert property ($past(valid && ($past(wcnt)==3'd7)) |-> (wlast_7==$past(last) && wdata_7==$past(data)));

  // Banks are stable when not written
  assert property ($past(!(valid && ($past(wcnt)==3'd0))) |-> (wlast_0==$past(wlast_0) && wdata_0==$past(wdata_0)));
  assert property ($past(!(valid && ($past(wcnt)==3'd1))) |-> (wlast_1==$past(wlast_1) && wdata_1==$past(wdata_1)));
  assert property ($past(!(valid && ($past(wcnt)==3'd2))) |-> (wlast_2==$past(wlast_2) && wdata_2==$past(wdata_2)));
  assert property ($past(!(valid && ($past(wcnt)==3'd3))) |-> (wlast_3==$past(wlast_3) && wdata_3==$past(wdata_3)));
  assert property ($past(!(valid && ($past(wcnt)==3'd4))) |-> (wlast_4==$past(wlast_4) && wdata_4==$past(wdata_4)));
  assert property ($past(!(valid && ($past(wcnt)==3'd5))) |-> (wlast_5==$past(wlast_5) && wdata_5==$past(wdata_5)));
  assert property ($past(!(valid && ($past(wcnt)==3'd6))) |-> (wlast_6==$past(wlast_6) && wdata_6==$past(wdata_6)));
  assert property ($past(!(valid && ($past(wcnt)==3'd7))) |-> (wlast_7==$past(wlast_7) && wdata_7==$past(wdata_7)));

  // Combinational mux correctness
  assert property ((rcnt==3'd0) |-> (inf_last_s==wlast_0 && inf_data_s==wdata_0));
  assert property ((rcnt==3'd1) |-> (inf_last_s==wlast_1 && inf_data_s==wdata_1));
  assert property ((rcnt==3'd2) |-> (inf_last_s==wlast_2 && inf_data_s==wdata_2));
  assert property ((rcnt==3'd3) |-> (inf_last_s==wlast_3 && inf_data_s==wdata_3));
  assert property ((rcnt==3'd4) |-> (inf_last_s==wlast_4 && inf_data_s==wdata_4));
  assert property ((rcnt==3'd5) |-> (inf_last_s==wlast_5 && inf_data_s==wdata_5));
  assert property ((rcnt==3'd6) |-> (inf_last_s==wlast_6 && inf_data_s==wdata_6));
  assert property (((rcnt==3'd7)) |-> (inf_last_s==wlast_7 && inf_data_s==wdata_7));

  // Ready side combinational
  assert property (inf_ready_s == (inf_ready | ~inf_valid));

  // Read-side state machine: advance when data available and ready_s
  // Advance case
  assert property ($past(inf_ready_s && ($past(rcnt) != $past(wcnt))) |-> 
                   (rcnt==$past(rcnt)+3'd1 && inf_valid && inf_last==$past(inf_last_s) && inf_data==$past(inf_data_s)));
  // Empty case
  assert property ($past(inf_ready_s && ($past(rcnt) == $past(wcnt))) |-> 
                   (rcnt==$past(rcnt) && !inf_valid && !inf_last && inf_data=='0));
  // Hold under backpressure
  assert property ($past(!inf_ready_s) |-> 
                   (rcnt==$past(rcnt) && inf_valid==$past(inf_valid) && inf_last==$past(inf_last) && inf_data==$past(inf_data)));

  // Output invariants
  assert property (!inf_valid |-> (!inf_last && inf_data=='0));
  assert property ((inf_valid && !inf_ready) |=> (inf_valid && rcnt==$past(rcnt) && inf_last==$past(inf_last) && inf_data==$past(inf_data)));

  // Shadow counters to check depth and pointer low bits
  logic [15:0] wcount, rcount;
  logic [15:0] outstanding;
  wire adv = (inf_ready_s && (rcnt != wcnt));

  always_ff @(posedge clk) begin
    if (rst) begin
      wcount <= '0;
      rcount <= '0;
    end else begin
      if (valid) wcount <= wcount + 16'd1;
      if (adv)   rcount <= rcount + 16'd1;
    end
  end

  assign outstanding = wcount - rcount;

  // Pointers match low bits of shadow counters
  assert property (wcnt == wcount[2:0]);
  assert property (rcnt == rcount[2:0]);

  // No overflow usage (depth 8). Change to assume if desired.
  assert property (outstanding <= 16'd8);

  // Coverage
  cover property (valid[*8]); // 8 consecutive writes
  cover property (adv[*8]);   // 8 consecutive reads/advances
  cover property (inf_valid && !inf_ready [*3] ##1 (inf_valid && inf_ready)); // backpressure then handshake
  cover property ($rose(wcnt==3'd0) && $past(wcnt)==3'd7); // write wrap
  cover property ($rose(rcnt==3'd0) && $past(rcnt)==3'd7); // read wrap
  cover property ($past(adv) && inf_last); // last observed on an output transfer

endmodule

// Bind example (uncomment in TB or a bind file):
// bind ad_axis_inf_rx ad_axis_inf_rx_sva #(.DATA_WIDTH(DATA_WIDTH)) i_ad_axis_inf_rx_sva(.*);