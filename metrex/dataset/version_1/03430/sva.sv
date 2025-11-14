// SVA checker for crc
module crc_sva (
  input logic        clk,
  input logic        rst,
  input logic        crc_en,
  input logic [15:0] data_in,
  input logic [15:0] crc_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Track availability of a $past() sample
  logic past_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Functional update when enabled (single-cycle update)
  property p_enable_update;
    crc_en |-> (crc_out == (data_in + 16'hA001));
  endproperty
  assert property (p_enable_update)
    else $error("crc_out mismatch when crc_en=1");

  // Hold value when not enabled
  property p_hold_when_disabled;
    past_valid && !crc_en |-> (crc_out == $past(crc_out));
  endproperty
  assert property (p_hold_when_disabled)
    else $error("crc_out changed while crc_en=0");

  // Output must be known post-reset
  assert property (past_valid |-> !$isunknown(crc_out))
    else $error("crc_out is X/Z after reset release");

  // Inputs must be known when used
  assert property (crc_en |-> !$isunknown(data_in))
    else $error("data_in is X/Z when crc_en=1");

  // Reset dominance at clock edge
  assert property (@(posedge clk) rst |-> (crc_out == 16'h0000))
    else $error("crc_out not 0 on clk edge while rst=1");

  // Asynchronous reset clears immediately
  assert property (@(posedge rst) (crc_out == 16'h0000))
    else $error("crc_out not 0 on async rst");

  // Coverage
  cover property (past_valid && crc_en && (crc_out == (data_in + 16'hA001))); // enabled update
  cover property (past_valid && !crc_en ##1 !crc_en);                         // hold across cycles
  cover property (!rst ##1 rst ##1 !rst);                                     // reset pulse
  cover property (past_valid && crc_en ##1 crc_en);                           // back-to-back enables
endmodule

// Bind to DUT
bind crc crc_sva u_crc_sva (.clk(clk), .rst(rst), .crc_en(crc_en), .data_in(data_in), .crc_out(crc_out));