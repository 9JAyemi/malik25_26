// SVA for fifo_generator
// Quality-focused, concise checks and coverage across both clk and s_aclk domains.

module fifo_generator_sva #(
  parameter WIDTH = 5,
  parameter DEPTH = 1024,
  parameter ADDR_WIDTH = $clog2(DEPTH)
)(
  input  logic                   clk,
  input  logic                   s_aclk,
  input  logic                   rst,         // active-high normal operation, active-low reset
  input  logic                   s_aresetn,   // active-low reset
  input  logic [WIDTH-1:0]       din,
  input  logic                   rd_en,
  input  logic                   wr_en,
  input  logic [WIDTH-1:0]       dout,
  input  logic                   empty,
  input  logic                   full,
  // internal DUT state
  input  logic [ADDR_WIDTH-1:0]  wptr,
  input  logic [ADDR_WIDTH-1:0]  rptr,
  input  logic [ADDR_WIDTH-1:0]  next_wptr,
  input  logic [ADDR_WIDTH-1:0]  next_rptr,
  input  logic [31:0]            slow_cnt,
  input  logic [31:0]            slow_wr_cnt,
  input  logic [31:0]            slow_rd_cnt,
  input  logic                   slow_wr_en,
  input  logic                   slow_rd_en
);

  // Handy locals
  localparam int HALF = DEPTH/2;

  // Basic safety: flags mutual exclusion
  assert property (@(posedge clk) !(full && empty));

  // Reset behavior (clk domain)
  assert property (@(posedge clk) !rst |-> (wptr==0 && rptr==0));
  assert property (@(posedge clk) !rst |=> ($stable(wptr) && $stable(rptr)));

  // Pointers monotonic (0 or +1 step per clk when out of reset)
  assert property (@(posedge clk) disable iff (!rst)
                   $past(rst) |-> (wptr == $past(wptr) || wptr == $past(wptr)+1));
  assert property (@(posedge clk) disable iff (!rst)
                   $past(rst) |-> (rptr == $past(rptr) || rptr == $past(rptr)+1));

  // No illegal ops at boundaries (protocol intent)
  assert property (@(posedge clk) disable iff (!rst) !(wr_en && full));
  assert property (@(posedge clk) disable iff (!rst) !(rd_en && empty));

  // Flag correctness vs pointers (one-slot-empty FIFO)
  assert property (@(posedge clk) (empty == (wptr==rptr)));
  assert property (@(posedge clk) (full  == ((wptr+1'b1)==rptr)));

  // Data integrity: a written item must be returned when its address is read
  // (captures address and data at write, checks matching read later)
  property p_data_integrity;
    logic [ADDR_WIDTH-1:0] a;
    logic [WIDTH-1:0]      d;
    @(posedge clk) disable iff (!rst)
      (wr_en && !full, a = wptr, d = din)
      |-> ##[1:$] (rd_en && !empty && rptr==a && dout==d);
  endproperty
  assert property (p_data_integrity);

  // Minimal scoreboard for occupancy and ordering
  logic [WIDTH-1:0] q[$];
  int unsigned occ;
  wire wr_fire = rst && wr_en && !full;
  wire rd_fire = rst && rd_en && !empty;

  always_ff @(posedge clk) begin
    if (!rst) begin
      q.delete();
      occ <= 0;
    end else begin
      if (wr_fire) begin
        q.push_back(din);
        occ <= occ + 1;
      end
      if (rd_fire) begin
        if (q.size() > 0) begin
          assert (dout == q[0])
            else $error("FIFO data mismatch: expected %0h got %0h", q[0], dout);
          q.pop_front();
        end
        if (occ > 0) occ <= occ - 1;
      end
    end
  end

  // Occupancy vs flags bounds (capacity = DEPTH-1 with one-slot-empty)
  assert property (@(posedge clk) disable iff (!rst) occ <= (DEPTH-1));
  assert property (@(posedge clk) disable iff (!rst) (empty == (occ==0)));
  assert property (@(posedge clk) disable iff (!rst) (full  == (occ==(DEPTH-1))));

  // Slower clock domain checks
  // Reset
  assert property (@(posedge s_aclk) !s_aresetn |-> (slow_cnt==0 && slow_wr_cnt==0 && slow_rd_cnt==0));

  // Counters increment as coded
  assert property (@(posedge s_aclk) disable iff (!s_aresetn) (slow_cnt == $past(slow_cnt) + 1));
  assert property (@(posedge s_aclk) disable iff (!s_aresetn) (slow_wr_cnt == $past(slow_wr_cnt) + wr_en));
  assert property (@(posedge s_aclk) disable iff (!s_aresetn) (slow_rd_cnt == $past(slow_rd_cnt) + rd_en));

  // slow_en combinational correctness
  assert property (@(posedge s_aclk) disable iff (!s_aresetn) (slow_wr_en == (slow_wr_cnt < HALF)));
  assert property (@(posedge s_aclk) disable iff (!s_aresetn) (slow_rd_en == (slow_rd_cnt < HALF)));

  // next_* update logic (as coded)
  assert property (@(posedge s_aclk) disable iff (!s_aresetn)
                   (slow_cnt==0) |-> (next_wptr == ((slow_wr_en && wr_en) ? (wptr+1'b1) : wptr)));
  assert property (@(posedge s_aclk) disable iff (!s_aresetn)
                   (slow_cnt==0) |-> (next_rptr == ((slow_rd_en && rd_en) ? (rptr+1'b1) : rptr)));
  assert property (@(posedge s_aclk) disable iff (!s_aresetn)
                   (slow_cnt!=0) |-> (next_wptr == wptr && next_rptr == rptr));

  // Coverage (essential scenarios)
  cover property (@(posedge clk) !rst ##1 rst);                                   // clk reset release
  cover property (@(posedge s_aclk) !s_aresetn ##1 s_aresetn);                    // s_aclk reset release
  cover property (@(posedge clk) disable iff (!rst) wr_fire);                     // write occurs
  cover property (@(posedge clk) disable iff (!rst) rd_fire);                     // read occurs
  cover property (@(posedge clk) disable iff (!rst) empty ##1 !empty);            // leave empty
  cover property (@(posedge clk) disable iff (!rst) !full ##[1:$] full);          // reach full
  cover property (@(posedge clk) disable iff (!rst)
                  ($past(wptr)=={ADDR_WIDTH{1'b1}}) && (wptr=={ADDR_WIDTH{1'b0}})); // wptr wrap
  cover property (@(posedge clk) disable iff (!rst)
                  ($past(rptr)=={ADDR_WIDTH{1'b1}}) && (rptr=={ADDR_WIDTH{1'b0}})); // rptr wrap
  cover property (@(posedge clk) disable iff (!rst) wr_fire && rd_fire);          // simultaneous rd/wr
  cover property (@(posedge s_aclk) disable iff (!s_aresetn)
                  (slow_wr_en && !($past(slow_wr_en))) or (!slow_wr_en && $past(slow_wr_en))); // toggle slow_wr_en
  cover property (@(posedge s_aclk) disable iff (!s_aresetn)
                  (slow_rd_en && !($past(slow_rd_en))) or (!slow_rd_en && $past(slow_rd_en))); // toggle slow_rd_en

endmodule

// Bind into DUT; connects to internal signals for deep checks
bind fifo_generator fifo_generator_sva #(
  .WIDTH(WIDTH),
  .DEPTH(DEPTH),
  .ADDR_WIDTH(ADDR_WIDTH)
) fifo_generator_sva_i (
  .clk        (clk),
  .s_aclk     (s_aclk),
  .rst        (rst),
  .s_aresetn  (s_aresetn),
  .din        (din),
  .rd_en      (rd_en),
  .wr_en      (wr_en),
  .dout       (dout),
  .empty      (empty),
  .full       (full),
  .wptr       (wptr),
  .rptr       (rptr),
  .next_wptr  (next_wptr),
  .next_rptr  (next_rptr),
  .slow_cnt   (slow_cnt),
  .slow_wr_cnt(slow_wr_cnt),
  .slow_rd_cnt(slow_rd_cnt),
  .slow_wr_en (slow_wr_en),
  .slow_rd_en (slow_rd_en)
);