// SVA checker for fifo_address_sync
module fifo_address_sync_sva #(parameter C_ADDRESS_WIDTH = 4) (
  input  logic                         clk,
  input  logic                         resetn,

  input  logic                         m_axis_ready,
  input  logic                         m_axis_valid,
  input  logic [C_ADDRESS_WIDTH-1:0]   m_axis_raddr,
  input  logic [C_ADDRESS_WIDTH-1:0]   m_axis_raddr_next,
  input  logic [C_ADDRESS_WIDTH:0]     m_axis_level,

  input  logic                         s_axis_ready,
  input  logic                         s_axis_valid,
  input  logic                         s_axis_empty,
  input  logic [C_ADDRESS_WIDTH-1:0]   s_axis_waddr,
  input  logic [C_ADDRESS_WIDTH:0]     s_axis_room
);

  localparam int AW = C_ADDRESS_WIDTH;
  localparam logic [AW:0] DEPTH = {1'b1, {AW{1'b0}}}; // 2**AW
  localparam logic [AW-1:0] MAX_PTR = {AW{1'b1}};
  localparam logic [AW:0] DEPTHm1 = DEPTH - 1'b1;

  wire read  = m_axis_ready & m_axis_valid;
  wire write = s_axis_ready & s_axis_valid;

  // Reset values
  property p_reset_values;
    @(posedge clk)
      !resetn |-> (m_axis_valid==1'b0 && s_axis_ready==1'b0 &&
                   m_axis_level=={(AW+1){1'b0}} && s_axis_room==DEPTH &&
                   s_axis_empty==1'b0 && s_axis_waddr=={AW{1'b0}} &&
                   m_axis_raddr=={AW{1'b0}});
  endproperty
  assert property (p_reset_values);

  // No X on key signals after reset
  assert property (@(posedge clk) disable iff (!resetn)
    !$isunknown({m_axis_valid, s_axis_ready, s_axis_empty,
                 m_axis_raddr, m_axis_raddr_next, s_axis_waddr,
                 m_axis_level, s_axis_room}));

  // Capacity invariants
  assert property (@(posedge clk) disable iff (!resetn)
    (m_axis_level <= DEPTH) && (s_axis_room <= DEPTH));
  assert property (@(posedge clk) disable iff (!resetn)
    (m_axis_level + s_axis_room) == DEPTH);
  assert property (@(posedge clk) disable iff (!resetn)
    s_axis_room == (DEPTH - m_axis_level));

  // Output flag consistency
  assert property (@(posedge clk) disable iff (!resetn)
    m_axis_valid == (m_axis_level != '0));
  assert property (@(posedge clk) disable iff (!resetn)
    s_axis_ready == (m_axis_level != DEPTH));
  assert property (@(posedge clk) disable iff (!resetn)
    s_axis_empty == (m_axis_level == '0));

  // No underflow/overflow handshakes
  assert property (@(posedge clk) disable iff (!resetn)
    (m_axis_level == '0) |-> !read);
  assert property (@(posedge clk) disable iff (!resetn)
    (m_axis_level == DEPTH) |-> !write);

  // Level state update
  assert property (@(posedge clk) disable iff (!resetn)
    $past(resetn) |-> m_axis_level
      == $past(m_axis_level)
         + ($past(write) ? 1 : 0)
         - ($past(read)  ? 1 : 0));

  // Read address next is combinational function of read
  assert property (@(posedge clk)
    m_axis_raddr_next == (m_axis_raddr + (read ? 1 : 0)));

  // Read/write address updates
  assert property (@(posedge clk) disable iff (!resetn)
    $past(resetn) |-> m_axis_raddr
      == ($past(m_axis_raddr) + ($past(read) ? 1 : 0)));
  assert property (@(posedge clk) disable iff (!resetn)
    $past(resetn) |-> s_axis_waddr
      == ($past(s_axis_waddr) + ($past(write) ? 1 : 0)));

  // When no op, pointers and level hold
  assert property (@(posedge clk) disable iff (!resetn)
    $past(resetn) && !$past(read) && !$past(write) |-> (
      m_axis_level == $past(m_axis_level) &&
      m_axis_raddr == $past(m_axis_raddr) &&
      s_axis_waddr == $past(s_axis_waddr)));

  // Coverage
  cover property (@(posedge clk) disable iff (!resetn) read);
  cover property (@(posedge clk) disable iff (!resetn) write);
  cover property (@(posedge clk) disable iff (!resetn) read && write);
  cover property (@(posedge clk) disable iff (!resetn) m_axis_level == '0);
  cover property (@(posedge clk) disable iff (!resetn) m_axis_level == DEPTH);
  cover property (@(posedge clk) disable iff (!resetn)
    (m_axis_level == '0) ##[1:$] (m_axis_level == DEPTH));
  cover property (@(posedge clk) disable iff (!resetn)
    (m_axis_level == DEPTH) ##[1:$] (m_axis_level == '0));
  cover property (@(posedge clk) disable iff (!resetn)
    $past(write) && $past(s_axis_waddr)==MAX_PTR && (s_axis_waddr=='0));
  cover property (@(posedge clk) disable iff (!resetn)
    $past(read) && $past(m_axis_raddr)==MAX_PTR && (m_axis_raddr=='0));
  cover property (@(posedge clk) disable iff (!resetn)
    (m_axis_level inside {[1:DEPTHm1]}) && read && write);

endmodule

// Bind example:
// bind fifo_address_sync fifo_address_sync_sva #(.C_ADDRESS_WIDTH(C_ADDRESS_WIDTH)) u_fifo_address_sync_sva (.*);