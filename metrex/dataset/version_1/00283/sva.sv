// Bindable SVA checker for LIFO
module LIFO_sva #(parameter int data_width = 8, parameter int depth = 16) ();

  // Use DUT scope signals directly (bind inside LIFO)
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Handshake qualifies
  wire wr_fire = wr_en && (count < depth);
  wire rd_fire = rd_en && (count > 0);

  // 1) Reset behavior
  assert property (@(posedge clk) rst |-> (top==0 && bottom==0 && count==0));

  // 2) Count bounds (never exceed depth)
  assert property (count <= depth);

  // 3) Next-state correctness for count (must reflect +/- of accepted ops)
  assert property (1'b1 |=> count == $past(count)
                                 + ($past(wr_en) && ($past(count) < depth) ? 1:0)
                                 - ($past(rd_en) && ($past(count) > 0) ? 1:0));

  // 4) Pointers change only on accepted ops and with correct delta
  assert property ($past(wr_fire) |=> top == $past(top) + 1);
  assert property (!$past(wr_fire) |=> top == $past(top));
  assert property ($past(rd_fire) |=> bottom == $past(bottom) + 1);
  assert property (!$past(rd_fire) |=> bottom == $past(bottom));

  // 5) Memory index safety whenever accessing memory
  assert property (wr_fire |-> top < depth);
  assert property (rd_fire |-> bottom < depth);

  // 6) Blocked op must not change state
  assert property ($past(wr_en) && ($past(count)==depth)
                   |=> (top==$past(top) && count==$past(count)));
  assert property ($past(rd_en) && ($past(count)==0)
                   |=> (bottom==$past(bottom) && count==$past(count) && dout==$past(dout)));

  // 7) dout only updates on accepted read
  assert property (!$past(rd_fire) |=> dout == $past(dout));

  // 8) Structural invariant: count equals (top - bottom)
  assert property (count == (top - bottom));

  // 9) Functional LIFO scoreboard (golden stack)
  logic [data_width-1:0] ref_stack [0:depth-1];
  integer sp;
  initial sp = 0;

  // Track pushes (use pre-increment sp as write index)
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      sp <= 0;
    end else begin
      if (wr_fire) begin
        assert (sp < depth) else $error("Reference stack overflow");
        ref_stack[sp] <= din;
      end
      // update stack pointer atomically: sp_next = sp + wr - rd
      sp <= sp + (wr_fire ? 1:0) - (rd_fire ? 1:0);
      if (rd_fire) begin
        assert ($past(sp) > 0) else $error("Reference stack underflow");
      end
    end
  end

  // Compare pop data on next cycle to last pushed data
  assert property (rd_fire |=> dout == $past(ref_stack[$past(sp)-1]));

  // 10) Useful coverage
  cover property (rst ##1 !rst ##1 wr_fire[*depth] ##1 rd_fire[*depth]); // fill then drain
  cover property (!rst ##1 wr_fire and rd_fire);                         // simultaneous op
  cover property (!rst ##1 (wr_en && (count==depth)) );                  // overflow attempt
  cover property (!rst ##1 (rd_en && (count==0)) );                      // underflow attempt

endmodule

// Bind into the DUT
bind LIFO LIFO_sva #(.data_width(data_width), .depth(depth)) LIFO_sva_i();