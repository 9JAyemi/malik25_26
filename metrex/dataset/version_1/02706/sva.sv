// SVA checker for fifo
module fifo_sva #(parameter int DEPTH=8, parameter int WIDTH=16)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [WIDTH-1:0]  din,
  input  logic              wr_en,
  input  logic              rd_en,
  input  logic [WIDTH-1:0]  dout,
  input  logic              empty,
  input  logic              full
);

  // Handshake events (accepted ops)
  wire wr_fire = wr_en && !full;
  wire rd_fire = rd_en && !empty;

  // Lightweight reference model (scoreboard)
  logic [WIDTH-1:0] q[$];
  int unsigned occ;
  logic [WIDTH-1:0] exp_d;
  logic             exp_v;

  // Model the FIFO semantics: pop then push on each cycle
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      q.delete();
      occ   <= 0;
      exp_v <= 0;
      exp_d <= '0;
    end else begin
      // read side
      if (rd_fire) begin
        if (q.size() > 0) begin
          exp_d <= q[0];
          q.pop_front();
          exp_v <= 1;
        end else begin
          exp_v <= 0; // underflow attempt (covered/asserted below)
        end
      end else begin
        exp_v <= 0;
      end
      // write side
      if (wr_fire) begin
        q.push_back(din);
      end
      occ <= q.size();
    end
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic flag sanity
  assert property (!(empty && full)) else $error("empty and full both high");

  // Flags must reflect occupancy exactly
  assert property (empty == (occ == 0)) else $error("empty flag mismatch");
  assert property (full  == (occ == DEPTH)) else $error("full flag mismatch");
  assert property ((occ > 0 && occ < DEPTH) |-> (!empty && !full)) else $error("interior occupancy flags wrong");

  // Occupancy evolution equals accepted ops
  assert property ($past(!rst) |-> occ == $past(occ) + ($past(wr_fire)?1:0) - ($past(rd_fire)?1:0))
    else $error("occupancy update mismatch");
  assert property (occ <= DEPTH) else $error("occupancy exceeded depth");

  // Data ordering/integrity: next cycle dout equals popped data
  assert property (exp_v |-> (dout === exp_d)) else $error("dout mismatch with expected data");

  // No read accepted -> dout must hold its value
  assert property (!rd_fire |=> $stable(dout)) else $error("dout changed without a read");

  // Optional robustness: attempts while full/empty
  assert property (full && wr_en |=> full) else $error("full must not be broken by blocked write");
  assert property (empty && rd_en |=> $stable(dout)) else $error("dout changed on empty read attempt");

  // Coverage: fill to full, drain to empty, simultaneous ops, overflow/underflow attempts
  cover property ((wr_fire && !rd_fire)[*DEPTH] ##1 full);
  cover property ((rd_fire && !wr_fire)[*DEPTH] ##1 empty);
  cover property (wr_fire && rd_fire);
  cover property (full && wr_en);   // write attempt while full
  cover property (empty && rd_en);  // read attempt while empty

endmodule

// Bind into DUT
bind fifo fifo_sva #(.DEPTH(8), .WIDTH(16)) fifo_sva_i
(
  .clk(clk),
  .rst(rst),
  .din(din),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .dout(dout),
  .empty(empty),
  .full(full)
);