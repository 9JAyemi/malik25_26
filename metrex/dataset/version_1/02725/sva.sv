// SVA for tmu2_mask
// Bind into DUT or instantiate alongside

module tmu2_mask_sva (
  input  logic              sys_clk,
  input  logic              sys_rst,

  input  logic              busy,

  input  logic              pipe_stb_i,
  input  logic              pipe_ack_o,
  input  logic              pipe_ack_i,

  input  logic              pipe_stb_o,

  input  logic  signed [11:0] dx,
  input  logic  signed [11:0] dy,
  input  logic  signed [17:0] tx,
  input  logic  signed [17:0] ty,

  input  logic  [17:0]      tex_hmask,
  input  logic  [17:0]      tex_vmask,

  input  logic  signed [11:0] dx_f,
  input  logic  signed [11:0] dy_f,
  input  logic  signed [17:0] tx_m,
  input  logic  signed [17:0] ty_m
);

  // Reset invariants
  assert property (@(posedge sys_clk) sys_rst |-> (pipe_stb_o==1'b0 && busy==1'b0 && pipe_ack_o==1'b1))
    else $error("Reset invariants violated");

  // Combinational definitions
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   pipe_ack_o == (~pipe_stb_o | pipe_ack_i))
    else $error("pipe_ack_o definition mismatch");

  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   busy == pipe_stb_o)
    else $error("busy must equal pipe_stb_o");

  // Handshake shorthand
  sequence hs; pipe_stb_i && pipe_ack_o; endsequence

  // Accept: capture and assert pipe_stb_o next cycle
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   hs |=> (pipe_stb_o
                          && dx_f == $past(dx)
                          && dy_f == $past(dy)
                          && tx_m == ($past(tx) & $past(tex_hmask))
                          && ty_m == ($past(ty) & $past(tex_vmask))))
    else $error("Capture/mask on accept failed");

  // Clear when downstream acks and no new accept in same cycle
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   (pipe_ack_i && !hs) |=> !pipe_stb_o)
    else $error("pipe_stb_o must clear on pipe_ack_i without new accept");

  // No change when neither accept nor clear
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   !(pipe_ack_i || hs) |=> $stable({pipe_stb_o, dx_f, dy_f, tx_m, ty_m}))
    else $error("State changed without accept or clear");

  // Handshake gating behavior of ack_o
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   !pipe_stb_o |-> pipe_ack_o)
    else $error("ack_o must be 1 when not busy");

  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   pipe_stb_o |-> (pipe_ack_o == pipe_ack_i))
    else $error("When busy, ack_o must mirror pipe_ack_i");

  // Edge-based causality
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   $rose(pipe_stb_o) |-> $past(hs))
    else $error("pipe_stb_o rose without an accept");

  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   $fell(pipe_stb_o) |-> $past(pipe_ack_i && !hs))
    else $error("pipe_stb_o fell without downstream ack (and no simultaneous accept)");

  // Coverage
  cover property (@(posedge sys_clk) disable iff (sys_rst) hs);                                   // accept
  cover property (@(posedge sys_clk) disable iff (sys_rst) hs ##1 hs);                           // back-to-back accepts
  cover property (@(posedge sys_clk) disable iff (sys_rst) $past(pipe_stb_o) && hs);             // accept while busy
  cover property (@(posedge sys_clk) disable iff (sys_rst) pipe_stb_o ##1 (pipe_ack_i && !hs) ##1 !pipe_stb_o); // clear
  cover property (@(posedge sys_clk) disable iff (sys_rst) !pipe_stb_o && hs);                   // accept from idle
  cover property (@(posedge sys_clk) disable iff (sys_rst)
                  hs && (($past(tx) & ~$past(tex_hmask)) != 18'd0 || ($past(ty) & ~$past(tex_vmask)) != 18'd0)); // masking effect observed

endmodule

// Example bind (place in a separate file or below after DUT is compiled)
// bind tmu2_mask tmu2_mask_sva tmu2_mask_sva_i (.*);