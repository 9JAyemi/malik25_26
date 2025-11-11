// SVA for multiply/controller_m/datapath_m
// Bind these modules to the DUT to check functionality and provide concise coverage.

// Controller checks
module controller_m_sva(
  input logic clock, reset, start, Zero,
  input logic Ready, Load_regs, Add_dec
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Combinational relationships
  assert property (Load_regs == (Ready && start));
  assert property (Ready |-> !Add_dec);
  assert property (!Ready |-> (Add_dec == !Zero));
  assert property (Add_dec |-> !Zero);
  assert property (!Ready |-> !Load_regs);

  // FSM behavior via Ready/Zero/Add_dec
  assert property (Ready && !start |=> Ready);      // stay Idle without start
  assert property (Ready && start |-> Load_regs);   // load on start
  assert property (Ready && start |=> !Ready);      // go Busy next cycle
  assert property (!Ready && !Zero |-> Add_dec);    // keep adding while !Zero
  assert property (!Ready && !Zero |=> !Ready);     // stay Busy
  assert property (!Ready && Zero |-> !Add_dec);    // stop add on Zero
  assert property (!Ready && Zero |=> Ready);       // return to Idle

  // Basic operation coverage
  cover property (Ready && start ##1 !Ready ##[1:$] Zero ##1 Ready);
endmodule

bind controller_m controller_m_sva controller_m_sva_i(
  .clock(clock), .reset(reset), .start(start), .Zero(Zero),
  .Ready(Ready), .Load_regs(Load_regs), .Add_dec(Add_dec)
);

// Datapath checks
module datapath_m_sva(
  input logic clock, reset,
  input logic [7:0] multiplicand, multiplier,
  input logic Load_regs, Add_dec,
  input logic [15:0] PR,
  input logic Zero,
  input logic [7:0] AR, BR
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Reset clears (checked next clock after async assertion)
  assert property ($rose(reset) |=> (AR==8'h00 && BR==8'h00 && PR==16'h0000));

  // Zero reflects AR==0
  assert property (Zero == (AR==8'h00));

  // Load behavior (sample inputs at load)
  assert property (Load_regs |=> (PR==16'h0000 && AR==$past(multiplier) && BR==$past(multiplicand)));

  // Add/dec behavior and safety
  assert property (Add_dec |-> ($past(AR)!=8'h00));
  assert property (Add_dec |=> (PR==$past(PR)+$past(BR) && AR==$past(AR)-8'h01 && BR==$past(BR)));

  // Stability when no action
  assert property (!Load_regs && !Add_dec |=> (AR==$past(AR) && BR==$past(BR) && PR==$past(PR)));

  // Progress guarantee (complete within 256 cycles)
  assert property (Load_regs |-> ##[1:256] Zero);

  // Corner-case coverage
  cover property (Load_regs ##1 Zero);               // multiplier==0 path
  cover property (Load_regs ##1 Add_dec ##1 Zero);   // multiplier==1 path
endmodule

bind datapath_m datapath_m_sva datapath_m_sva_i(
  .clock(clock), .reset(reset),
  .multiplicand(multiplicand), .multiplier(multiplier),
  .Load_regs(Load_regs), .Add_dec(Add_dec),
  .PR(PR), .Zero(Zero), .AR(AR), .BR(BR)
);

// Top-level cross-module checks and coverage
module multiply_sva(
  input logic clock, reset, start,
  input logic [7:0] multiplicand, multiplier,
  input logic [15:0] PR,
  input logic Ready, Load_regs, Add_dec, Zero
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Capture operands at load
  logic [7:0] multA, multB;
  always_ff @(posedge clock or posedge reset) begin
    if (reset) begin
      multA <= '0; multB <= '0;
    end else if (Load_regs) begin
      multA <= multiplicand;
      multB <= multiplier;
    end
  end

  // Final product correctness when Ready rises
  assert property ($rose(Ready) |-> (PR == multA * multB) && Zero && !Add_dec);

  // Handshake sanity
  assert property (Load_regs |-> Ready && start);
  assert property (Add_dec |-> !Ready);

  // Coverage: 0, 1, and multi-cycle cases
  cover property (Load_regs && (multiplier==8'h00) ##1 $rose(Ready) && PR==16'h0000);
  cover property (Load_regs && (multiplier==8'h01) ##1 Add_dec ##1 $rose(Ready) && PR==multA);
  cover property (Load_regs && (multiplier>8'h01) ##1 Add_dec ##1 Add_dec ##[1:$] $rose(Ready));
endmodule

bind multiply multiply_sva multiply_sva_i(
  .clock(clock), .reset(reset), .start(start),
  .multiplicand(multiplicand), .multiplier(multiplier),
  .PR(PR), .Ready(Ready), .Load_regs(Load_regs), .Add_dec(Add_dec), .Zero(Zero)
);