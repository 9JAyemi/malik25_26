// SystemVerilog Assertions for fifo_address_sync
// Concise, high-quality checks and coverage

module fifo_address_sync_sva #(
  parameter ADDRESS_WIDTH = 4
) (
  input  logic                     clk,
  input  logic                     resetn,

  input  logic                     m_axis_ready,
  input  logic                     m_axis_valid,
  input  logic [ADDRESS_WIDTH-1:0] m_axis_raddr,
  input  logic [ADDRESS_WIDTH:0]   m_axis_level,

  input  logic                     s_axis_ready,
  input  logic                     s_axis_valid,
  input  logic                     s_axis_empty,
  input  logic [ADDRESS_WIDTH-1:0] s_axis_waddr,
  input  logic [ADDRESS_WIDTH:0]   s_axis_room
);

  localparam logic [ADDRESS_WIDTH:0] MAX_ROOM = {1'b1, {ADDRESS_WIDTH{1'b0}}};

  wire read  = m_axis_ready & m_axis_valid;
  wire write = s_axis_ready & s_axis_valid;

  // Reset behavior (checked during reset)
  assert property (@(posedge clk)
    !resetn |-> (m_axis_level=='0 && s_axis_room==MAX_ROOM &&
                 m_axis_valid==1'b0 && s_axis_ready==1'b0 && s_axis_empty==1'b0 &&
                 m_axis_raddr=='0 && s_axis_waddr=='0));

  // One cycle after reset release
  assert property (@(posedge clk)
    $rose(resetn) |=> (m_axis_level=='0 && s_axis_room==MAX_ROOM &&
                       m_axis_valid==1'b0 && s_axis_ready==1'b1 && s_axis_empty==1'b1 &&
                       m_axis_raddr=='0 && s_axis_waddr=='0));

  // Invariants and flag relations
  assert property (@(posedge clk) disable iff(!resetn)
    m_axis_level <= MAX_ROOM);

  assert property (@(posedge clk) disable iff(!resetn)
    s_axis_room == (MAX_ROOM - m_axis_level));

  assert property (@(posedge clk) disable iff(!resetn)
    m_axis_valid == (m_axis_level != '0));

  assert property (@(posedge clk) disable iff(!resetn)
    s_axis_ready == (m_axis_level != MAX_ROOM));

  assert property (@(posedge clk) disable iff(!resetn)
    s_axis_empty == (m_axis_level == '0));

  // Read/Write legality at boundaries
  assert property (@(posedge clk) disable iff(!resetn)
    (m_axis_level=='0) |-> !read);

  assert property (@(posedge clk) disable iff(!resetn)
    (m_axis_level==MAX_ROOM) |-> !write);

  // Level update rules
  assert property (@(posedge clk) disable iff(!resetn)
    ($past(read) && !$past(write)) |-> (m_axis_level == $past(m_axis_level) - 1));

  assert property (@(posedge clk) disable iff(!resetn)
    (!$past(read) && $past(write)) |-> (m_axis_level == $past(m_axis_level) + 1));

  assert property (@(posedge clk) disable iff(!resetn)
    ($past(read) == $past(write)) |-> (m_axis_level == $past(m_axis_level)));

  // Pointer behavior
  assert property (@(posedge clk) disable iff(!resetn)
    read |-> (m_axis_raddr == $past(m_axis_raddr) + 1));

  assert property (@(posedge clk) disable iff(!resetn)
    !read |-> (m_axis_raddr == $past(m_axis_raddr)));

  assert property (@(posedge clk) disable iff(!resetn)
    write |-> (s_axis_waddr == $past(s_axis_waddr) + 1));

  assert property (@(posedge clk) disable iff(!resetn)
    !write |-> (s_axis_waddr == $past(s_axis_waddr)));

  // No X on key outputs after reset
  assert property (@(posedge clk) disable iff(!resetn)
    !$isunknown({m_axis_valid, s_axis_ready, s_axis_empty,
                 m_axis_raddr, s_axis_waddr, m_axis_level, s_axis_room}));

  // Coverage: empty->write->nonempty
  cover property (@(posedge clk) disable iff(!resetn)
    (m_axis_level=='0) ##1 (write && !read) ##1 (m_axis_level=='d1));

  // Coverage: full->read->not-full
  cover property (@(posedge clk) disable iff(!resetn)
    (m_axis_level==MAX_ROOM) ##1 (read && !write) ##1 (m_axis_level==MAX_ROOM-1));

  // Coverage: simultaneous read & write keeps level constant, increments both pointers
  cover property (@(posedge clk) disable iff(!resetn)
    (read && write) ##1 (m_axis_level == $past(m_axis_level) &&
                         m_axis_raddr == $past(m_axis_raddr)+1 &&
                         s_axis_waddr == $past(s_axis_waddr)+1));

  // Coverage: waddr and raddr wrap-around
  cover property (@(posedge clk) disable iff(!resetn)
    (write && $past(s_axis_waddr)=={ADDRESS_WIDTH{1'b1}}) ##1 (s_axis_waddr=='0));

  cover property (@(posedge clk) disable iff(!resetn)
    (read && $past(m_axis_raddr)=={ADDRESS_WIDTH{1'b1}}) ##1 (m_axis_raddr=='0));

endmodule

// Bind into the DUT
bind fifo_address_sync fifo_address_sync_sva #(.ADDRESS_WIDTH(ADDRESS_WIDTH)) fifo_address_sync_sva_i (
  .clk(clk),
  .resetn(resetn),
  .m_axis_ready(m_axis_ready),
  .m_axis_valid(m_axis_valid),
  .m_axis_raddr(m_axis_raddr),
  .m_axis_level(m_axis_level),
  .s_axis_ready(s_axis_ready),
  .s_axis_valid(s_axis_valid),
  .s_axis_empty(s_axis_empty),
  .s_axis_waddr(s_axis_waddr),
  .s_axis_room(s_axis_room)
);