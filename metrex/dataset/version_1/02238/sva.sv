// SVA checker for SERIAL_OUT
// Quality-focused, concise checks and coverage

module serial_out_sva (
  input  logic        CLK,
  input  logic        RESET,
  input  logic        READY,
  input  logic [7:0]  BYTEIN,
  input  logic        RX_D,
  input  logic        READ,
  input  logic        CLEAR,
  input  logic [4:0]  ADDR,
  input  logic [6:0]  count,
  input  logic [9:0]  data_out
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESET);

  // Sanity: no X after reset deasserts
  assert property (!$isunknown({RX_D, READ, CLEAR, ADDR, count, data_out})));

  // Async reset values must be seen after deassertion edge
  assert property (@(posedge CLK) !RESET |-> (count==7'd0 && ADDR==5'd0 && CLEAR==1'b1 && READ==1'b0 && RX_D==1'b1));

  // READY low behavior
  assert property (!READY |-> (RX_D==1'b1 && CLEAR==1'b1 && ADDR==5'd0));
  assert property (!READY |=> count == $past(count));

  // Internal shift register load on READY
  assert property (READY |-> data_out == {1'b1, BYTEIN, 1'b0});

  // Count progression while READY
  assert property (READY && count <= 7'd8 |=> count == $past(count) + 7'd1);
  assert property (READY && count == 7'd9 |=> count == 7'd0);
  assert property (READY |-> count <= 7'd9);

  // READ pulse generation and duration
  assert property (READY && count==7'd9 |-> READ && RX_D==1'b1);
  assert property (READY && count!=7'd9 |-> !READ);
  assert property ($past(READY && count==7'd9) |=> !READ);

  // Serialized output mapping
  assert property (READY && count==7'd0 |-> RX_D==1'b0);
  assert property (READY && count inside {[7'd1:7'd8]} |-> RX_D==BYTEIN[count-1]);
  assert property (READY && count<=7'd8 |-> RX_D==data_out[count]);
  assert property (READY && count==7'd9 |-> RX_D==1'b1);

  // ADDR behavior
  assert property (READY && count==7'd8 |=> ADDR == $past(ADDR) + 5'd1);          // modulo-32 via 5-bit truncation
  assert property ($past(READY && count==7'd8) && $past(ADDR)==5'd31 |=> ADDR==5'd0); // explicit wrap check

  // Intent check: CLEAR should deassert on ADDR wrap (likely RTL bug: compares ADDR==32)
  assert property ($past(READY && count==7'd8) && $past(ADDR)==5'd31 |-> CLEAR==1'b0)
    else $error("Intent: CLEAR should go low on ADDR wrap (ADDR 31->0 at count==8). RTL likely uses wrong compare.");

  // Otherwise CLEAR stays high
  assert property (!($past(READY && count==7'd8) && $past(ADDR)==5'd31) |-> CLEAR==1'b1);

  // Coverage: full frame under continuous READY leading to READ pulse
  cover property (READY && count==7'd0 ##9 (READY && count==7'd9 && READ));

  // Coverage: ADDR wrap occurs
  cover property ($past(READY && count==7'd8) && $past(ADDR)==5'd31 ##1 ADDR==5'd0);

  // Coverage: CLEAR deasserts (should not hit with current RTL, flags dead code)
  cover property (CLEAR==1'b0);

endmodule

// Bind into the DUT (connects to I/Os and internal regs by name)
bind SERIAL_OUT serial_out_sva sva_inst(.*);