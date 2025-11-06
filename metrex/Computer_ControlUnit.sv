Below is a bindable SVA checker that verifies reset behavior, instruction field capture, opcode-to-output decode (with the intended one-cycle latency), constant outputs, bus packing, and absence of X/Z, along with coverpoints for full functional coverage of all opcodes and the default case. It also includes a width sanity check to catch the CNTRL_bus_out packing mismatch.


// ============================================================
// SVA checker for Computer_ControlUnit
// Bind this module to the DUT (bind statement shown below).
// ============================================================

module Computer_ControlUnit_sva #(
  parameter DR_WIDTH = 3,
  parameter SA_WIDTH = DR_WIDTH,
  parameter SB_WIDTH = DR_WIDTH,
  parameter OPCODE_WIDTH = 7,
  parameter FS_WIDTH = 4,
  parameter CNTRL_FLAGS_WIDTH = 7,
  parameter ULA_FLAG_WIDTH = 4,
  parameter CNTRL_WIDTH = DR_WIDTH+SA_WIDTH+SB_WIDTH+FS_WIDTH+CNTRL_FLAGS_WIDTH
)(
  // DUT clocks/resets
  input  logic                          CLK,
  input  logic                          RST,

  // DUT inputs
  input  logic [15:0]                   INSTR_bus_in,
  input  logic [ULA_FLAG_WIDTH-1:0]     ULA_FLAG_bus_in,
  input  logic [15:0]                   ADDR_bus_in,

  // DUT outputs
  input  logic [7:0]                    CONST_bus_out,
  input  logic [6:0]                    CNTRL_bus_out,     // DUT declaration
  input  logic [2:0]                    COUNTER_bus_out,

  // DUT internal registers (bound in)
  input  logic [DR_WIDTH-1:0]           DR,
  input  logic [SA_WIDTH-1:0]           SA,
  input  logic [SB_WIDTH-1:0]           SB,
  input  logic [OPCODE_WIDTH-1:0]       OPCODE,
  input  logic [FS_WIDTH-1:0]           FS,
  input  logic [CNTRL_FLAGS_WIDTH-1:0]  CNTRL_FLAGS
);

  // ------------------------------------------------------------
  // Compile/elaboration-time sanity checks (widths)
  // ------------------------------------------------------------
  initial begin
    if ($bits(CNTRL_bus_out) != CNTRL_WIDTH) begin
      $warning("CNTRL_bus_out width (%0d) != expected CNTRL_WIDTH (%0d). Assignment will be truncated to %0d LSBs.",
               $bits(CNTRL_bus_out), CNTRL_WIDTH, $bits(CNTRL_bus_out));
      $warning("Given DUT code, CNTRL_bus_out will equal CNTRL_FLAGS due to truncation.");
    end
  end

  // ------------------------------------------------------------
  // Default clocking/disable for properties below
  // ------------------------------------------------------------
  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // ------------------------------------------------------------
  // Asynchronous reset clears internal regs immediately on posedge RST
  // ------------------------------------------------------------
  // Because the DUT uses @(posedge CLK or posedge RST), the registers are set to 0
  // at the posedge RST event.
  assert property (@(posedge RST)
    (DR == '0 && SA == '0 && SB == '0 && OPCODE == '0 && FS == '0 && CNTRL_FLAGS == '0)
  ) else $error("Async reset failed to clear internal regs at posedge RST.");

  // ------------------------------------------------------------
  // No X/Z on key signals after reset deasserts
  // ------------------------------------------------------------
  assert property (
    !$isunknown({DR,SA,SB,OPCODE,FS,CNTRL_FLAGS,CONST_bus_out,CNTRL_bus_out,COUNTER_bus_out})
  ) else $error("Unknown (X/Z) detected on internal/output signals.");

  // ------------------------------------------------------------
  // Registering of instruction fields on each CLK (synchronous sampling)
  // ------------------------------------------------------------
  assert property (DR == INSTR_bus_in[15:13])
    else $error("DR does not match INSTR_bus_in[15:13] on clock.");
  assert property (SA == INSTR_bus_in[12:10])
    else $error("SA does not match INSTR_bus_in[12:10] on clock.");
  assert property (SB == INSTR_bus_in[9:7])
    else $error("SB does not match INSTR_bus_in[9:7] on clock.");
  assert property (OPCODE == INSTR_bus_in[6:0])
    else $error("OPCODE does not match INSTR_bus_in[6:0] on clock.");

  // ------------------------------------------------------------
  // Decode mapping with 1-cycle latency:
  // FS, CNTRL_FLAGS are driven by the previous cycle's opcode
  // ------------------------------------------------------------
  // ADD (0000000) -> FS=0001, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000000 |-> (FS == 4'b0001 && CNTRL_FLAGS == 7'b0000001) )
    else $error("ADD decode mismatch (1-cycle latency).");
  // SUB (0000001) -> FS=0010, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000001 |-> (FS == 4'b0010 && CNTRL_FLAGS == 7'b0000001) )
    else $error("SUB decode mismatch (1-cycle latency).");
  // AND (0000010) -> FS=0100, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000010 |-> (FS == 4'b0100 && CNTRL_FLAGS == 7'b0000001) )
    else $error("AND decode mismatch (1-cycle latency).");
  // OR  (0000011) -> FS=0101, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000011 |-> (FS == 4'b0101 && CNTRL_FLAGS == 7'b0000001) )
    else $error("OR decode mismatch (1-cycle latency).");
  // XOR (0000100) -> FS=0110, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000100 |-> (FS == 4'b0110 && CNTRL_FLAGS == 7'b0000001) )
    else $error("XOR decode mismatch (1-cycle latency).");
  // NOT (0000101) -> FS=0111, CNTRL_FLAGS=0000001
  assert property ( $past(OPCODE) == 7'b0000101 |-> (FS == 4'b0111 && CNTRL_FLAGS == 7'b0000001) )
    else $error("NOT decode mismatch (1-cycle latency).");
  // LD  (0000110) -> FS=0000, CNTRL_FLAGS=0000000
  assert property ( $past(OPCODE) == 7'b0000110 |-> (FS == 4'b0000 && CNTRL_FLAGS == 7'b0000000) )
    else $error("LD decode mismatch (1-cycle latency).");
  // ST  (0000111) -> FS=0000, CNTRL_FLAGS=0000010
  assert property ( $past(OPCODE) == 7'b0000111 |-> (FS == 4'b0000 && CNTRL_FLAGS == 7'b0000010) )
    else $error("ST decode mismatch (1-cycle latency).");
  // Default case (all others) -> FS=0000, CNTRL_FLAGS=0000000
  assert property ( ($past(OPCODE) inside {[7'b0001000:7'b1111111]}) |-> (FS == 4'b0000 && CNTRL_FLAGS == 7'b0000000) )
    else $error("Default decode mismatch (1-cycle latency).");

  // ------------------------------------------------------------
  // Cross-check: CNTRL_FLAGS may only be 0, 1, or 2 given DUT decode
  // ------------------------------------------------------------
  assert property (CNTRL_FLAGS inside {7'b0000000,7'b0000001,7'b0000010})
    else $error("CNTRL_FLAGS took an illegal value.");

  // If FS indicates an ALU op (ADD,SUB,AND,OR,XOR,NOT), then CNTRL_FLAGS must be 1
  assert property ( (FS inside {4'b0001,4'b0010,4'b0100,4'b0101,4'b0110,4'b0111}) |-> (CNTRL_FLAGS == 7'b0000001) )
    else $error("FS indicates ALU op but CNTRL_FLAGS != 1.");

  // If previous opcode is not ST and FS==0, CNTRL_FLAGS must be 0 (LD or default)
  assert property ( (FS == 4'b0000 && $past(OPCODE) != 7'b0000111) |-> (CNTRL_FLAGS == 7'b0000000) )
    else $error("FS==0 without ST but CNTRL_FLAGS != 0.");

  // ------------------------------------------------------------
  // Constant outputs must remain constant every cycle after reset
  // ------------------------------------------------------------
  assert property (CONST_bus_out == 8'h00)
    else $error("CONST_bus_out is not constant 8'h00.");

  assert property (COUNTER_bus_out == 3'b000)
    else $error("COUNTER_bus_out is not constant 3'b000.");

  // ------------------------------------------------------------
  // Control bus packing check (intended behavior)
  // NOTE: This will FAIL with the current DUT because CNTRL_bus_out is only 7 bits
  // while {DR,SA,SB,FS,CNTRL_FLAGS} is CNTRL_WIDTH (=20) bits.
  // ------------------------------------------------------------
  assert property (CNTRL_bus_out == {DR, SA, SB, FS, CNTRL_FLAGS})
    else $error("CNTRL_bus_out does not equal {DR,SA,SB,FS,CNTRL_FLAGS} (check bus width/order).");

  // If width mismatch exists, document the actual (truncated) behavior, for observability
  // This assertion confirms the current hardware effect and can be removed once width is fixed.
  generate
    if ($bits(CNTRL_bus_out) != CNTRL_WIDTH) begin : gen_trunc_obs
      assert property (CNTRL_bus_out == CNTRL_FLAGS[6:0])
        else $error("Given width mismatch, CNTRL_bus_out should equal CNTRL_FLAGS[6:0] due to truncation.");
    end
  endgenerate

  // ------------------------------------------------------------
  // Coverage: ensure every opcode path and default path is observed
  // ------------------------------------------------------------
  // A reset event
  cover property (@(posedge RST) 1);

  // Observe capture of each opcode in OPCODE (1-cycle later effects are implied)
  cover property ( $rose(!RST) ##1 $past(OPCODE) == 7'b0000000 ); // ADD
  cover property ( $past(OPCODE) == 7'b0000001 ); // SUB
  cover property ( $past(OPCODE) == 7'b0000010 ); // AND
  cover property ( $past(OPCODE) == 7'b0000011 ); // OR
  cover property ( $past(OPCODE) == 7'b0000100 ); // XOR
  cover property ( $past(OPCODE) == 7'b0000101 ); // NOT
  cover property ( $past(OPCODE) == 7'b0000110 ); // LD
  cover property ( $past(OPCODE) == 7'b0000111 ); // ST
  cover property ( $past(OPCODE) inside {[7'b0001000:7'b1111111]} ); // default-range opcode

  // Cover correct decode outcomes (FS,CNTRL_FLAGS) to ensure outputs were observed
  cover property ( $past(OPCODE) == 7'b0000000 && FS==4'b0001 && CNTRL_FLAGS==7'b0000001 ); // ADD decode observed
  cover property ( $past(OPCODE) == 7'b0000001 && FS==4'b0010 && CNTRL_FLAGS==7'b0000001 ); // SUB
  cover property ( $past(OPCODE) == 7'b0000010 && FS==4'b0100 && CNTRL_FLAGS==7'b0000001 ); // AND
  cover property ( $past(OPCODE) == 7'b0000011 && FS==4'b0101 && CNTRL_FLAGS==7'b0000001 ); // OR
  cover property ( $past(OPCODE) == 7'b0000100 && FS==4'b0110 && CNTRL_FLAGS==7'b0000001 ); // XOR
  cover property ( $past(OPCODE) == 7'b0000101 && FS==4'b0111 && CNTRL_FLAGS==7'b0000001 ); // NOT
  cover property ( $past(OPCODE) == 7'b0000110 && FS==4'b0000 && CNTRL_FLAGS==7'b0000000 ); // LD
  cover property ( $past(OPCODE) == 7'b0000111 && FS==4'b0000 && CNTRL_FLAGS==7'b0000010 ); // ST
  cover property ( ($past(OPCODE) inside {[7'b0001000:7'b1111111]}) && FS==4'b0000 && CNTRL_FLAGS==7'b0000000 ); // default

endmodule


// ============================================================
// Example bind statement
// Place this in a testbench or a package compiled with the DUT
// ============================================================
// The bind connects both DUT IOs and internal regs to the checker.

bind Computer_ControlUnit Computer_ControlUnit_sva #(
  .DR_WIDTH(DR_WIDTH),
  .SA_WIDTH(SA_WIDTH),
  .SB_WIDTH(SB_WIDTH),
  .OPCODE_WIDTH(OPCODE_WIDTH),
  .FS_WIDTH(FS_WIDTH),
  .CNTRL_FLAGS_WIDTH(CNTRL_FLAGS_WIDTH),
  .ULA_FLAG_WIDTH(ULA_FLAG_WIDTH),
  .CNTRL_WIDTH(CNTRL_WIDTH)
) i_Computer_ControlUnit_sva (
  // Clk/Reset
  .CLK(CLK),
  .RST(RST),

  // DUT inputs
  .INSTR_bus_in(INSTR_bus_in),
  .ULA_FLAG_bus_in(ULA_FLAG_bus_in),
  .ADDR_bus_in(ADDR_bus_in),

  // DUT outputs
  .CONST_bus_out(CONST_bus_out),
  .CNTRL_bus_out(CNTRL_bus_out),
  .COUNTER_bus_out(COUNTER_bus_out),

  // Internal regs
  .DR(DR),
  .SA(SA),
  .SB(SB),
  .OPCODE(OPCODE),
  .FS(FS),
  .CNTRL_FLAGS(CNTRL_FLAGS)
);