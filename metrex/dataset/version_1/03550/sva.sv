// SVA for i2s_tx
module i2s_tx_sva #(
  parameter int WIDTH = 16
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic [WIDTH-1:0]     input_l_tdata,
  input  logic [WIDTH-1:0]     input_r_tdata,
  input  logic                 input_tvalid,
  input  logic                 input_tready,
  input  logic                 sck,
  input  logic                 ws,
  input  logic                 sd,
  input  logic [WIDTH-1:0]     l_data,
  input  logic [WIDTH-1:0]     r_data,
  input  logic [3:0]           bit_count,
  input  logic [1:0]           channel_count
);

  // Parameter sanity: bit_count is 4 bits -> supports up to 16
  initial assert (WIDTH <= 16)
    else $error("i2s_tx: WIDTH=%0d exceeds bit_count capacity (16)", WIDTH);

  // Synchronous reset values must hold while rst is asserted
  always @(posedge clk) if (rst) begin
    assert (input_tready==1'b0 && sck==1'b0 && ws==1'b0 && sd==1'b0 &&
            l_data=='0 && r_data=='0 && bit_count==0 && channel_count==0);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // SCK must toggle every cycle (free-running)
  a_sck_toggle:        assert property (sck == !$past(sck));

  // Ready/valid handshake behavior
  a_ready_when_idle:   assert property (!input_tvalid |-> input_tready);
  a_ready_hold_low:    assert property ((input_tvalid && input_tready) |-> !input_tready until_with (!input_tvalid));

  // Capture on handshake and counter/channel init
  a_capture: assert property ((input_tvalid && input_tready) |=> 
                              l_data==$past(input_l_tdata) && r_data==$past(input_r_tdata) &&
                              bit_count==0 && channel_count==0);

  // Data registers only change on handshake (or reset)
  a_data_only_on_hs:   assert property (!(input_tvalid && input_tready) |-> $stable(l_data) && $stable(r_data));

  // bit_count domain and ws toggle rule
  a_bitcount_bound:    assert property (bit_count < WIDTH);
  a_ws_only_on_wrap:   assert property ($changed(ws) |-> $past(bit_count)==WIDTH-1);

  // Progression when active (uses prior-cycle sck/ws due to NBA semantics in DUT)
  a_step_midword: assert property (($past(sck) && $past(ws) && $past(bit_count)!=WIDTH-1) |->
                                   bit_count==$past(bit_count)+1 && sd==1'b0 &&
                                   ws==$past(ws) && channel_count==$past(channel_count));

  a_wrap_endword: assert property (($past(sck) && $past(ws) && $past(bit_count)==WIDTH-1) |->
                                   bit_count==0 && ws!=$past(ws) && channel_count!=$past(channel_count) &&
                                   ( ($past(channel_count)==2'd0 && sd==l_data[0]) ||
                                     ($past(channel_count)==2'd1 && sd==r_data[0]) ));

  // Channel count limited to 0/1
  a_channel_domain: assert property (channel_count inside {2'd0,2'd1});

  // Liveness/progress: after a handshake, WS must toggle within a bounded time
  localparam int MAX_LAT = 4*WIDTH;
  a_progress: assert property ((input_tvalid && input_tready) |-> ##[1:MAX_LAT] $changed(ws));

  // Coverage
  c_handshake:    cover property (input_tvalid && input_tready);
  c_ws_toggle:    cover property ($changed(ws));
  c_wrap_L:       cover property (($past(sck) && $past(ws) && $past(bit_count)==WIDTH-1 && $past(channel_count)==0) |->
                                   channel_count==1 && ws!=$past(ws) && sd==l_data[0]);
  c_wrap_R:       cover property (($past(sck) && $past(ws) && $past(bit_count)==WIDTH-1 && $past(channel_count)==1) |->
                                   channel_count==0 && ws!=$past(ws) && sd==r_data[0]);

endmodule

// Bind into DUT (gives the SVA module access to DUT internals)
bind i2s_tx i2s_tx_sva #(.WIDTH(WIDTH)) i2s_tx_sva_i (.*);