// SystemVerilog Assertions for early_boot
// Concise, high-quality checks and coverage

module early_boot_sva (
  input  logic        CLK_I,
  input  logic        RST_I,

  // DUT outputs
  input  logic        CYC_O,
  input  logic [31:0] DAT_O,
  input  logic        STB_O,
  input  logic        WE_O,
  input  logic [31:2] ADR_O,
  input  logic [3:0]  SEL_O,
  input  logic        loading_finished_o,

  // DUT inputs
  input  logic [31:0] DAT_I,
  input  logic        ACK_I,
  input  logic        ERR_I,
  input  logic        RTY_I,

  // DUT internals
  input  logic [3:0]  state,
  input  logic [9:0]  wait_counter
);
  // Local copies of encodings/constants
  localparam logic [3:0]
    S_CHECK_STATUS      = 4'd0,
    S_CHECK_STATUS_2    = 4'd1,
    S_CHECK_STATUS_3    = 4'd2,
    S_SET_SIZE          = 4'd3,
    S_SET_SIZE_2        = 4'd4,
    S_SET_CONTROL       = 4'd5,
    S_SET_CONTROL_2     = 4'd6,
    S_CHECK_FINISHED    = 4'd7,
    S_CHECK_FINISHED_2  = 4'd8,
    S_CHECK_FINISHED_3  = 4'd9,
    S_FINISHED          = 4'd10;

  localparam logic [29:0]
    ADDR_STATUS  = 30'h3000_0000,
    ADDR_SIZE    = 30'h3000_0002,
    ADDR_CONTROL = 30'h3000_0003;

  default clocking cb @(posedge CLK_I); endclocking
  default disable iff (RST_I);

  // Basic invariants
  assert property (SEL_O == 4'hF);
  assert property (loading_finished_o == (state == S_FINISHED));
  assert property (STB_O |-> CYC_O);

  // Reset values (checked in-cycle with reset)
  assert property (@(posedge CLK_I) RST_I |-> (CYC_O==0 && STB_O==0 && WE_O==0 &&
                                               DAT_O==32'd0 && ADR_O==30'd0 &&
                                               state==S_CHECK_STATUS && wait_counter==10'd0));

  // State value legal range
  assert property (state inside {
    S_CHECK_STATUS, S_CHECK_STATUS_2, S_CHECK_STATUS_3,
    S_SET_SIZE, S_SET_SIZE_2, S_SET_CONTROL, S_SET_CONTROL_2,
    S_CHECK_FINISHED, S_CHECK_FINISHED_2, S_CHECK_FINISHED_3, S_FINISHED
  });

  // Command cycles: correct bus fields per state
  assert property (state==S_CHECK_STATUS     |-> (CYC_O && STB_O && !WE_O && ADR_O==ADDR_STATUS  && DAT_O==32'd0));
  assert property (state==S_SET_SIZE         |-> (CYC_O && STB_O &&  WE_O && ADR_O==ADDR_SIZE    && DAT_O==32'd2048));
  assert property (state==S_SET_CONTROL      |-> (CYC_O && STB_O &&  WE_O && ADR_O==ADDR_CONTROL && DAT_O==32'd2));
  assert property (state==S_CHECK_FINISHED   |-> (CYC_O && STB_O && !WE_O && ADR_O==ADDR_STATUS  && DAT_O==32'd0));

  // ACK-wait states hold the command (until ACK)
  assert property (state==S_CHECK_STATUS_2   && !ACK_I |-> (CYC_O && STB_O && !WE_O && ADR_O==ADDR_STATUS  && DAT_O==32'd0));
  assert property (state==S_SET_SIZE_2       && !ACK_I |-> (CYC_O && STB_O &&  WE_O && ADR_O==ADDR_SIZE    && DAT_O==32'd2048));
  assert property (state==S_SET_CONTROL_2    && !ACK_I |-> (CYC_O && STB_O &&  WE_O && ADR_O==ADDR_CONTROL && DAT_O==32'd2));
  assert property (state==S_CHECK_FINISHED_2 && !ACK_I |-> (CYC_O && STB_O && !WE_O && ADR_O==ADDR_STATUS  && DAT_O==32'd0));

  // Handshake behavior
  assert property ((CYC_O && STB_O && !ACK_I) |=> (CYC_O && STB_O && $stable({WE_O,ADR_O,DAT_O,SEL_O})));
  assert property ((CYC_O && STB_O &&  ACK_I) |=> (!CYC_O && !STB_O));

  // Deterministic next-state on command issue
  assert property (state==S_CHECK_STATUS   |=> state==S_CHECK_STATUS_2);
  assert property (state==S_SET_SIZE       |=> state==S_SET_SIZE_2);
  assert property (state==S_SET_CONTROL    |=> state==S_SET_CONTROL_2);
  assert property (state==S_CHECK_FINISHED |=> state==S_CHECK_FINISHED_2);

  // Deterministic next-state on ACKs
  assert property (state==S_CHECK_STATUS_2   && ACK_I && (DAT_I==32'd2)  |=> state==S_SET_SIZE);
  assert property (state==S_CHECK_STATUS_2   && ACK_I && (DAT_I!=32'd2)  |=> state==S_CHECK_STATUS_3);
  assert property (state==S_SET_SIZE_2       && ACK_I                    |=> state==S_SET_CONTROL);
  assert property (state==S_SET_CONTROL_2    && ACK_I                    |=> state==S_CHECK_FINISHED);
  assert property (state==S_CHECK_FINISHED_2 && ACK_I && (DAT_I==32'd2)  |=> state==S_FINISHED);
  assert property (state==S_CHECK_FINISHED_2 && ACK_I && (DAT_I!=32'd2)  |=> state==S_CHECK_FINISHED_3);

  // Wait-loop behavior and counter semantics; bus must be idle in wait states
  assert property (state==S_CHECK_STATUS_3   && wait_counter!=10'd1023 |=> state==S_CHECK_STATUS_3   && wait_counter==$past(wait_counter)+10'd1 && !CYC_O && !STB_O);
  assert property (state==S_CHECK_STATUS_3   && wait_counter==10'd1023 |=> state==S_CHECK_STATUS     && wait_counter==10'd0                     && !CYC_O && !STB_O);
  assert property (state==S_CHECK_FINISHED_3 && wait_counter!=10'd1023 |=> state==S_CHECK_FINISHED_3 && wait_counter==$past(wait_counter)+10'd1 && !CYC_O && !STB_O);
  assert property (state==S_CHECK_FINISHED_3 && wait_counter==10'd1023 |=> state==S_CHECK_FINISHED   && wait_counter==10'd0                     && !CYC_O && !STB_O);

  // Environment constraint (DUT has no handling for ERR/RTY)
  assume property (!CYC_O || (!ERR_I && !RTY_I));

  // Coverage
  cover property (state==S_FINISHED);
  cover property (state==S_CHECK_STATUS_3   ##[1:$] state==S_CHECK_STATUS);
  cover property (state==S_CHECK_FINISHED_3 ##[1:$] state==S_CHECK_FINISHED);
  cover property (state==S_SET_SIZE ##[1:$] state==S_SET_CONTROL ##[1:$] state==S_FINISHED);
  cover property (wait_counter==10'd1023);
endmodule

// Bind into DUT
bind early_boot early_boot_sva u_early_boot_sva (
  .CLK_I(CLK_I), .RST_I(RST_I),
  .CYC_O(CYC_O), .DAT_O(DAT_O), .STB_O(STB_O), .WE_O(WE_O), .ADR_O(ADR_O), .SEL_O(SEL_O),
  .loading_finished_o(loading_finished_o),
  .DAT_I(DAT_I), .ACK_I(ACK_I), .ERR_I(ERR_I), .RTY_I(RTY_I),
  .state(state), .wait_counter(wait_counter)
);