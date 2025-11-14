// SVA for tmu2_fifo64to256
// Quality-focused, concise checks and coverage. Bind into DUT.

module tmu2_fifo64to256_sva
(
  input  logic         sys_clk,
  input  logic         sys_rst,

  input  logic         we,
  input  logic [63:0]  wd,
  input  logic         re,
  output logic [255:0] rd,
  output logic         w8avail,
  output logic         ravail,

  // internal DUT signals
  input  logic                   wavail,
  input  logic [      :0]        level,   // sized by bind (wildcard)
  input  logic [      :0]        produce, // sized by bind
  input  logic [      :0]        consume, // sized by bind
  input  logic                   read,
  input  logic                   write
);

  // Derive capacities from actual RTL widths (portable across depth)
  localparam int L_W       = $bits(level);
  localparam int MAX64_CAP = 1 << (L_W-1);     // max number of 64b slots

  // Default clocking inlined per-assert
  // Reset behavior
  assert property (@(posedge sys_clk) sys_rst |-> (level==0 && produce==0 && consume==0));

  // Handshake/gating definitions
  assert property (@(posedge sys_clk) read  == (re && ravail));
  assert property (@(posedge sys_clk) write == (we && wavail));

  // Availability encodings
  assert property (@(posedge sys_clk) ravail == (level >= 4));
  assert property (@(posedge sys_clk) wavail == (level <  MAX64_CAP));
  assert property (@(posedge sys_clk) w8avail == (level < (MAX64_CAP-8)));

  // Safety bounds
  assert property (@(posedge sys_clk) disable iff (sys_rst) level <= MAX64_CAP);
  assert property (@(posedge sys_clk) disable iff (sys_rst) read |-> level >= 4);

  // Pointer updates (only on qualified ops)
  assert property (@(posedge sys_clk) disable iff (sys_rst) $past(write) |-> produce == $past(produce)+1);
  assert property (@(posedge sys_clk) disable iff (sys_rst) !$past(write) |-> produce == $past(produce));
  assert property (@(posedge sys_clk) disable iff (sys_rst) $past(read)  |-> consume == $past(consume)+1);
  assert property (@(posedge sys_clk) disable iff (sys_rst) !$past(read)  |-> consume == $past(consume));

  // Level exact update on all four cases
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   ($past(read) && !$past(write)) |-> level == $past(level)-4);
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   (!$past(read) && $past(write)) |-> level == $past(level)+1);
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   ($past(read) && $past(write))  |-> level == $past(level)-3);
  assert property (@(posedge sys_clk) disable iff (sys_rst)
                   (!$past(read) && !$past(write))|-> level == $past(level));

  // Data ordering and assembly scoreboard (64b queue -> 256b beat)
  logic [63:0] q[$];
  always_ff @(posedge sys_clk) begin
    if (sys_rst) begin
      q.delete();
    end else begin
      if (we && wavail) q.push_back(wd);

      if (re && ravail) begin
        assert(q.size() >= 4)
          else $error("TMU2 fifo: read without 4 entries in model queue");

        automatic logic [255:0] exp_rd = {q[0], q[1], q[2], q[3]};
        assert (rd === exp_rd)
          else $error("TMU2 fifo: RD mismatch. exp=%0h got=%0h", exp_rd, rd);

        // Pop four oldest 64b entries
        void'(q.pop_front());
        void'(q.pop_front());
        void'(q.pop_front());
        void'(q.pop_front());
      end
    end
  end

  // Model/DUT occupancy equivalence
  assert property (@(posedge sys_clk) disable iff (sys_rst) q.size() == level);

  // When data is advertised available, no X/Z on output
  assert property (@(posedge sys_clk) disable iff (sys_rst) ravail |-> !$isunknown(rd));

  // Minimal but meaningful coverage
  cover property (@(posedge sys_clk) disable iff (sys_rst) write && !read);
  cover property (@(posedge sys_clk) disable iff (sys_rst) read  && !write);
  cover property (@(posedge sys_clk) disable iff (sys_rst) read  &&  write);

  cover property (@(posedge sys_clk) disable iff (sys_rst)
                  (level == MAX64_CAP-1 && write && !read)); // reach full
  cover property (@(posedge sys_clk) disable iff (sys_rst) !w8avail); // near-full (<=7 slots left)

  cover property (@(posedge sys_clk) disable iff (sys_rst)
                  write && (produce[1:0]==2'd3) ##1 write && (produce[1:0]==2'd0)); // 64b-lane wrap

  cover property (@(posedge sys_clk) disable iff (sys_rst)
                  read && (consume == {($bits(consume)){1'b1}}) ##1 (consume == '0)); // index wrap
endmodule

bind tmu2_fifo64to256 tmu2_fifo64to256_sva sva_i
(
  .sys_clk,
  .sys_rst,
  .we,
  .wd,
  .re,
  .rd,
  .w8avail,
  .ravail,
  .wavail,
  .level,
  .produce,
  .consume,
  .read,
  .write
);