// SVA for timer
module timer_assertions
(
  input logic        CLK_I,
  input logic        RST_I,
  input logic [31:2] ADR_I,
  input logic        CYC_I,
  input logic        STB_I,
  input logic        WE_I,
  input logic        RTY_O,
  input logic        interrupt_o,
  input logic [27:0] counter
);

  localparam [27:0] TERM     = 28'h00FFFFF;
  localparam [29:0] ACK_ADDR = {27'h7FFFFFF, 3'b001};

  logic ack_hit;
  assign ack_hit = CYC_I && STB_I && !WE_I && (ADR_I == ACK_ADDR);

  // synchronous reset behavior must force known state
  assert property (@(posedge CLK_I) RST_I |-> (RTY_O==1'b0 && interrupt_o==1'b0 && counter==28'd0));

  default clocking cb @(posedge CLK_I); endclocking
  default disable iff (RST_I)

  logic past_valid;
  always @(posedge CLK_I) begin
    if (RST_I) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Below terminal: counter increments, RTY_O is 0, interrupt_o holds
  assert property (past_valid && $past(counter != TERM)
                   |-> (counter == $past(counter)+28'd1)
                       && (RTY_O == 1'b0)
                       && (interrupt_o == $past(interrupt_o)));

  // At terminal without valid ack: interrupt asserts, counter holds, RTY_O stable
  assert property (past_valid && $past(counter==TERM) && !($past(interrupt_o) && ack_hit)
                   |-> (counter==TERM) && (interrupt_o==1'b1) && (RTY_O==$past(RTY_O)));

  // Valid ack at terminal with interrupt pending: pulse RTY_O, clear interrupt and counter
  assert property (past_valid && $past(counter==TERM) && $past(interrupt_o) && ack_hit
                   |-> (RTY_O==1'b1) && (interrupt_o==1'b0) && (counter==28'd0));

  // RTY_O can only be asserted by the valid ack condition at terminal with interrupt pending
  assert property (RTY_O |-> (past_valid && $past(counter==TERM) && $past(interrupt_o) && ack_hit));

  // Interrupt stays asserted and counter stays at TERM until ack (or reset)
  assert property (past_valid && $past(interrupt_o) && !($past(interrupt_o) && ack_hit)
                   |-> (interrupt_o==1'b1) && (counter==TERM));

  // Coverage
  cover property (past_valid && $past(counter==TERM) && !($past(interrupt_o) && ack_hit) |-> interrupt_o);
  cover property (past_valid && $past(counter==TERM) && $past(interrupt_o) && ack_hit
                  |-> (RTY_O && (counter==28'd0) && !interrupt_o));
  cover property (past_valid && $past(counter==TERM) && !$past(interrupt_o) && ack_hit
                  |-> (interrupt_o && !RTY_O));

endmodule

bind timer timer_assertions sva(
  .CLK_I(CLK_I),
  .RST_I(RST_I),
  .ADR_I(ADR_I),
  .CYC_I(CYC_I),
  .STB_I(STB_I),
  .WE_I(WE_I),
  .RTY_O(RTY_O),
  .interrupt_o(interrupt_o),
  .counter(counter)
);