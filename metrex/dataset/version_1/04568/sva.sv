// SVA for digital_clock
module digital_clock_sva #(
  parameter int CLK_FREQ   = 50_000_000,
  parameter int MIN_FREQ   = 60,
  parameter int HOUR_FREQ  = 24,
  parameter int BCD_WIDTH  = 5,
  parameter int SEG_WIDTH  = 7,
  parameter int DISP_WIDTH = 4
)(
  input  logic                          clk,
  input  logic                          reset,
  input  logic [BCD_WIDTH-1:0]          hours,
  input  logic [BCD_WIDTH-1:0]          minutes,
  input  logic [SEG_WIDTH*DISP_WIDTH-1:0] seg,
  input  logic [DISP_WIDTH-1:0]         an,
  // internal regs
  input  logic [BCD_WIDTH-1:0]          hours_reg,
  input  logic [BCD_WIDTH-1:0]          minutes_reg
);

  // Static sanity checks
  initial begin
    assert (BCD_WIDTH==5 && SEG_WIDTH==7 && DISP_WIDTH==4)
      else $error("Parameter mismatch: expected BCD_WIDTH=5, SEG_WIDTH=7, DISP_WIDTH=4");
    assert (MIN_FREQ==60 && HOUR_FREQ==24)
      else $error("Parameter mismatch: expected MIN_FREQ=60, HOUR_FREQ=24");
  end

  // Constants for seg mapping
  localparam logic [27:0] SEG_R = {7'b1111110, 7'b0000000, 7'b0000000, 7'b0000000};
  localparam logic [27:0] SEG_SR= {7'b1111110, 7'b1111110, 7'b0000000, 7'b0000000};
  localparam logic [27:0] SEG_SL= {7'b1111110, 7'b1111110, 7'b1111110, 7'b0000000};
  localparam logic [27:0] SEG_L = {7'b1111110, 7'b1111110, 7'b1111110, 7'b1111110};
  localparam logic [27:0] SEG_Z = {28{1'b0}};

  default clocking cb @(posedge clk); endclocking
  // Use explicit disable iff on each property where needed

  // Reset drives known values on next clock
  property p_reset_vals;
    @(posedge clk) reset |=> (hours_reg=='0 && minutes_reg=='0 && seg==SEG_Z && an==4'b1111);
  endproperty
  assert property (p_reset_vals);

  // No X/Z after reset deasserts
  assert property (@(posedge clk) disable iff (reset) !$isunknown({hours_reg, minutes_reg, seg, an}));

  // Ranges (will flag width/rollover issues)
  assert property (@(posedge clk) disable iff (reset) hours_reg  < HOUR_FREQ);
  assert property (@(posedge clk) disable iff (reset) minutes_reg < MIN_FREQ);

  // Hours stable except at minute rollover
  assert property (@(posedge clk) disable iff (reset)
                   (minutes_reg != '0) |-> (hours_reg == $past(hours_reg)));

  // Minutes increment by +1 except when rolling over
  assert property (@(posedge clk) disable iff (reset)
                   (minutes_reg != '0) |-> (minutes_reg == $past(minutes_reg)+1));

  // Minute rollover -> hour increments (with wrap at 24)
  assert property (@(posedge clk) disable iff (reset)
                   ($past(minutes_reg) == MIN_FREQ-1) |-> (minutes_reg=='0 &&
                     (hours_reg == $past(hours_reg)+1 ||
                      ($past(hours_reg) == HOUR_FREQ-1 && hours_reg=='0))));

  // Hour rollover only occurs on minute rollover
  assert property (@(posedge clk) disable iff (reset)
                   (hours_reg=='0 && $past(hours_reg)!=0) |-> ($past(minutes_reg)==MIN_FREQ-1 && minutes_reg=='0));

  // an must be from allowed set after reset
  assert property (@(posedge clk) disable iff (reset)
                   an inside {4'b1110,4'b1101,4'b1011,4'b0111});

  // an rotation next-state mapping (uses previous an)
  assert property (@(posedge clk) disable iff (reset)
                   ( ($past(an)==4'b1110 && an==4'b1101) ||
                     ($past(an)==4'b1101 && an==4'b1011) ||
                     ($past(an)==4'b1011 && an==4'b0111) ||
                     ($past(an)==4'b0111 && an==4'b1110) ||
                     ((!($past(an) inside {4'b1110,4'b1101,4'b1011,4'b0111})) && an==4'b1110) ));

  // seg value must match mapping from previous an
  assert property (@(posedge clk) disable iff (reset)
                   ( ($past(an)==4'b1110 && seg==SEG_R ) ||
                     ($past(an)==4'b1101 && seg==SEG_SR) ||
                     ($past(an)==4'b1011 && seg==SEG_SL) ||
                     ($past(an)==4'b0111 && seg==SEG_L ) ||
                     ((!($past(an) inside {4'b1110,4'b1101,4'b1011,4'b0111})) && seg==SEG_Z) ));

  // Coverage
  // Minute rollover observed
  cover property (@(posedge clk) disable iff (reset)
                  $past(minutes_reg)==MIN_FREQ-1 && minutes_reg=='0);

  // Hour rollover observed (23->0 on minute rollover)
  cover property (@(posedge clk) disable iff (reset)
                  $past(hours_reg)==HOUR_FREQ-1 && hours_reg=='0 &&
                  $past(minutes_reg)==MIN_FREQ-1 && minutes_reg=='0);

  // an completes a full rotation
  sequence an_cycle;
    an==4'b1110 ##1 an==4'b1101 ##1 an==4'b1011 ##1 an==4'b0111 ##1 an==4'b1110;
  endsequence
  cover property (@(posedge clk) disable iff (reset) an_cycle);

  // seg default path exercised (after invalid an)
  cover property (@(posedge clk) reset ##1 (seg==SEG_Z && an==4'b1110));
endmodule

// Bind into the DUT
bind digital_clock digital_clock_sva #(
  .CLK_FREQ  (CLK_FREQ),
  .MIN_FREQ  (MIN_FREQ),
  .HOUR_FREQ (HOUR_FREQ),
  .BCD_WIDTH (BCD_WIDTH),
  .SEG_WIDTH (SEG_WIDTH),
  .DISP_WIDTH(DISP_WIDTH)
) u_digital_clock_sva (
  .clk        (clk),
  .reset      (reset),
  .hours      (hours),
  .minutes    (minutes),
  .seg        (seg),
  .an         (an),
  .hours_reg  (hours_reg),
  .minutes_reg(minutes_reg)
);