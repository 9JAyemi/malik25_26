// SVA checker for fifo_buffer
// Bind this in your testbench: bind fifo_buffer fifo_buffer_sva #(.DEPTH(DEPTH), .ADDRW(ADDRW), .SW(SW)) i_fifo_buffer_sva (.*);

module fifo_buffer_sva #(parameter int DEPTH=256, ADDRW=8, SW=4)
(
  input  logic                 clk,
  input  logic                 nrst,
  input  logic                 reset,
  input  logic [SW*2-1:0]      din,
  input  logic [SW*2-1:0]      dout,
  input  logic                 wr,
  input  logic                 rd,
  input  logic                 empty,
  input  logic                 full,
  // internal DUT state (visible in bind scope)
  input  logic [ADDRW:0]       waddr,
  input  logic [ADDRW:0]       raddr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!nrst);

  // Convenience
  localparam int W = ADDRW;
  wire [W-1:0] waddr_i = waddr[W-1:0];
  wire [W-1:0] raddr_i = raddr[W-1:0];

  // Protocol: no overflow/underflow
  assert property (!(wr && full && !rd));
  assert property (!(rd && empty && !wr));

  // Reset behavior
  assert property (reset |-> (waddr==0 && raddr==0 && empty && !full));
  assert property (!nrst |-> (waddr==0 && raddr==0));

  // Pointers increment and hold (when not in reset)
  assert property (!reset && wr |=> waddr == $past(waddr)+1);
  assert property (!reset && rd |=> raddr == $past(raddr)+1);
  assert property (!reset && !wr |=> waddr == $past(waddr));
  assert property (!reset && !rd |=> raddr == $past(raddr));
  // Wrap MSB toggles
  assert property (!reset && wr && $past(waddr_i)=={W{1'b1}} |=> waddr[W] != $past(waddr[W]) && waddr_i=='0);
  assert property (!reset && rd && $past(raddr_i)=={W{1'b1}} |=> raddr[W] != $past(raddr[W]) && raddr_i=='0);

  // Flag correctness and mutual exclusion
  assert property (empty == ((waddr[W] ~^ raddr[W]) && (waddr_i == raddr_i)));
  assert property (full  == ((waddr[W]  ^ raddr[W]) && (waddr_i == raddr_i)));
  assert property (!(empty && full));

  // Model occupancy to cross-check flags
  logic [W:0] occ;
  always_ff @(posedge clk or negedge nrst) begin
    if (!nrst)                       occ <= '0;
    else if (reset)                  occ <= '0;
    else case ({wr && !full, rd && !empty})
      2'b10: occ <= occ + 1;
      2'b01: occ <= occ - 1;
      default: occ <= occ;
    endcase
  end
  assert property (occ <= DEPTH);
  assert property (empty == (occ==0));
  assert property (full  == (occ==DEPTH));
  assert property (!reset && wr && rd && !full && !empty |=> occ == $past(occ));

  // Data ordering/intactness scoreboard
  logic [SW*2-1:0] q[$];
  always_ff @(posedge clk or negedge nrst) begin
    if (!nrst || reset) q.delete();
    else begin
      if (wr && !full) q.push_back(din);
      if (rd && !empty) begin
        assert (q.size()>0) else $error("FIFO underflow vs. model");
        // With async read port and sync write, this samples pre-write data
        assert (dout == q[0]) else $error("FIFO data mismatch: dout != expected head");
        void'(q.pop_front());
      end
    end
  end

  // Useful coverage
  cover property (reset ##1 !reset && empty);
  cover property (empty ##[1:$] full);
  cover property (full ##[1:$] empty);
  cover property (wr && rd && !full && !empty);
  cover property (wr && $past(waddr_i)=={W{1'b1}});
  cover property (rd && $past(raddr_i)=={W{1'b1}});
  cover property (occ == (DEPTH/2));

endmodule