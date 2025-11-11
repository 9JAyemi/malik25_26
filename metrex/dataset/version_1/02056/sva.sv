// SVA for address_counter
module address_counter_sva #(parameter int COUNT_WIDTH = 13)
(
  input  logic        clk,
  input  logic        clken,
  input  logic        trig,
  input  logic [31:0] address,
  input  logic [3:0]  wen
);

  default clocking cb @(posedge clk); endclocking

  localparam int unsigned MAX_COUNT    = (1 << COUNT_WIDTH) - 1;
  localparam int unsigned MAX_ADDR_U32 = (MAX_COUNT << 2);
  localparam int unsigned ADDR_W       = COUNT_WIDTH + 2;

  // Helper: valid past
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Helper: detect wrap cycle (when wen samples trig_detected)
  wire wrap = (clken && address == MAX_ADDR_U32);

  // Helper scoreboard: any trig rising seen since last wrap (excluding current wrap cycle)
  bit seen_rise;
  always_ff @(posedge clk) begin
    if (wrap)            seen_rise <= 1'b0;
    else if ($rose(trig)) seen_rise <= 1'b1;
  end

  // Address basic shape
  assert property (address[1:0] == 2'b00);
  if (ADDR_W < 32) begin
    assert property (address[31:ADDR_W] == '0);
  end

  // Address progression
  assert property (past_valid && $past(!clken)        |-> address == $past(address));
  assert property (past_valid && $past(clken) && $past(address) != MAX_ADDR_U32
                   |-> address == $past(address) + 32'd4);
  assert property (past_valid && $past(clken) && $past(address) == MAX_ADDR_U32
                   |-> address == 32'd0);
  // Any address change must be due to prior clken
  assert property (past_valid && $changed(address) |-> $past(clken));

  // WEN must be replicated bit
  assert property (wen == {4{wen[0]}});

  // WEN can only change immediately after a wrap cycle
  assert property (past_valid && $changed(wen) |-> $past(wrap));

  // WEN value after wrap reflects whether a trig rising occurred since previous wrap (excluding current cycle)
  assert property (past_valid && $past(wrap) |-> wen == {4{$past(seen_rise)}});

  // Same-cycle trig rise at wrap must NOT assert wen
  assert property (past_valid && wrap && $rose(trig) |=> wen == 4'b0000);

  // Coverage
  cover property (past_valid && wrap); // observe at least one wrap
  cover property (past_valid && seen_rise ##1 wrap ##1 (wen == 4'b1111)); // wen asserted at wrap+1
  cover property (past_valid && (!seen_rise) ##1 wrap ##1 (wen == 4'b0000)); // wen deasserted at wrap+1
  cover property (past_valid && wrap && $rose(trig) ##1 (wen == 4'b0000)); // same-cycle trig with wrap

endmodule

bind address_counter address_counter_sva #(.COUNT_WIDTH(COUNT_WIDTH))
  address_counter_sva_i (.clk(clk), .clken(clken), .trig(trig), .address(address), .wen(wen));