// SVA for sasc_fifo4
// Quality-focused, concise checks and coverage
// Bind into the DUT to access internal pointers/gb

bind sasc_fifo4 sasc_fifo4_sva u_sasc_fifo4_sva (
  .clk   (clk),
  .rst   (rst),
  .clr   (clr),
  .din   (din),
  .we    (we),
  .dout  (dout),
  .re    (re),
  .full  (full),
  .empty (empty),
  .wp    (wp),
  .rp    (rp),
  .gb    (gb)
);

module sasc_fifo4_sva
(
  input  logic        clk, rst, clr,
  input  logic [7:0]  din, dout,
  input  logic        we, re,
  input  logic        full, empty,
  input  logic [1:0]  wp, rp,
  input  logic        gb
);

  // Default clock/reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst || clr);

  // --------------------------
  // Environment safety (no misuse)
  // --------------------------
  // No write when full unless read also occurring; no read when empty
  assert property (we |-> (!full || re)) else $error("Overflow write when full without read");
  assert property (re |-> !empty)        else $error("Underflow read when empty");

  // --------------------------
  // Reset/clear behavior
  // --------------------------
  assert property (!rst |-> (wp==2'd0 && rp==2'd0 && gb==1'b0));
  assert property (clr  |=> (wp==2'd0 && rp==2'd0 && gb==1'b0));

  // --------------------------
  // Pointer update rules
  // --------------------------
  assert property (we  |=> wp == $past(wp)+2'd1);
  assert property (!we |=> wp == $past(wp));

  assert property (re  |=> rp == $past(rp)+2'd1);
  assert property (!re |=> rp == $past(rp));

  // --------------------------
  // Guard-bit protocol and flags
  // --------------------------
  // gb set when a write makes wp_p1 == rp; cleared by re unless set condition also true
  assert property ( (we && ((wp+2'd1)==rp)) |=> gb );
  assert property ( (re && !(we && ((wp+2'd1)==rp))) |=> !gb );

  // Flags are mutually exclusive
  assert property (!(full && empty));

  // Flags consistent with gb/wp/rp
  assert property ( full  == ((wp==rp) && gb) );
  assert property ( empty == ((wp==rp) && !gb) );

  // --------------------------
  // Lightweight reference model (count + data queue)
  // --------------------------
  int unsigned count;
  bit [7:0] q[$];

  // Maintain model
  always_ff @(posedge clk or negedge rst) begin
    if (!rst) begin
      count <= 0;
      q.delete();
    end else if (clr) begin
      count <= 0;
      q.delete();
    end else begin
      // Push only if write is accepted (i.e., not blocked by overflow rule)
      if (we && (!full || re)) begin
        q.push_back(din);
      end
      // On read, must match head of model queue
      if (re) begin
        if (q.size() > 0) begin
          assert (dout === q[0]) else $error("Data mismatch on read: dout != expected");
          q.pop_front();
        end
      end
      // Update occupancy
      unique case ({we && (!full || re), re})
        2'b10: count <= count + 1; // write only
        2'b01: count <= (count>0) ? count - 1 : count; // read only (underflow protected by assertion)
        default: /* no change */ ;
      endcase
    end
  end

  // Count range and mapping to flags
  assert property (count <= 4);
  assert property (empty == (count==0));
  assert property (full  == (count==4));

  // Count vs pointer distance (mod-4)
  // For wp != rp, occupancy equals modulo distance; for equality, gb disambiguates 0 vs 4
  function automatic int md4(input logic [1:0] a, b);
    md4 = (a - b) & 2'd3;
  endfunction
  assert property ( (wp != rp) |-> (count == md4(wp,rp)) );
  assert property ( (wp == rp) |-> ((count==0) == (!gb)) );
  assert property ( (wp == rp) |-> ((count==4) == ( gb)) );

  // --------------------------
  // Wrap-around coverage and scenarios
  // --------------------------
  // Fill to full then drain to empty
  cover property ( empty ##1 (we && !re)[*4] ##1 full ##1 (re && !we)[*4] ##1 empty );

  // Pointer wrap on write/read
  cover property ( (wp==2'd3 && we) ##1 (wp==2'd0) );
  cover property ( (rp==2'd3 && re) ##1 (rp==2'd0) );

  // About-to-full guard-bit set event
  cover property ( we && ((wp+2'd1)==rp) );

  // Simultaneous read/write in middle occupancy
  cover property ( !full && !empty && we && re );

endmodule