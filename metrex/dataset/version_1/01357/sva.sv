// SVA for eth_clockgen
// Bind into the DUT to check functionality and provide coverage

module eth_clockgen_sva
(
  input  logic        Clk,
  input  logic        Reset,
  input  logic [7:0]  Divider,
  input  logic [7:0]  Counter,
  input  logic [7:0]  CounterPreset,
  input  logic [7:0]  TempDivider,
  input  logic        CountEq0,
  input  logic        Mdc,
  input  logic        MdcEn,
  input  logic        MdcEn_n
);

  default clocking cb @(posedge Clk); endclocking
  default disable iff (Reset);

  // Asynchronous reset values (sampled at clk edge while Reset is 1)
  assert property (@cb Reset |-> (Counter == 8'h01 && Mdc == 1'b0))
    else $error("Reset values incorrect");

  // No X/Z in key signals once out of reset
  assert property (@cb !$isunknown({Counter, CountEq0, Mdc, MdcEn, MdcEn_n}))
    else $error("Unknown detected on outputs/state");

  // Combinational relationships
  assert property (@cb TempDivider == ((Divider < 8'd2) ? 8'd2 : Divider))
    else $error("TempDivider max(2, Divider) mismatch");

  assert property (@cb CounterPreset == ((TempDivider >> 1) - 8'd1))
    else $error("CounterPreset computation mismatch");

  assert property (@cb CountEq0 == (Counter == 8'h00))
    else $error("CountEq0 inconsistent with Counter");

  // Counter state machine
  assert property (@cb CountEq0 |=> Counter == $past(CounterPreset))
    else $error("Counter reload mismatch");

  assert property (@cb !CountEq0 |=> Counter == ($past(Counter) - 8'd1))
    else $error("Counter decrement mismatch");

  // Mdc toggles only on CountEq0, and must toggle when CountEq0
  assert property (@cb CountEq0 |=> Mdc != $past(Mdc))
    else $error("Mdc failed to toggle on CountEq0");

  assert property (@cb !CountEq0 |=> Mdc == $past(Mdc))
    else $error("Mdc changed without CountEq0");

  // Spacing of CountEq0 pulses based on reload value
  // If reload is P, then next CountEq0 occurs exactly after P+1 cycles
  property p_eq0_spacing;
    int p;
    (CountEq0, p = CounterPreset + 1) |=> (!CountEq0)[*(p-1)] ##1 CountEq0;
  endproperty
  assert property (@cb p_eq0_spacing)
    else $error("CountEq0 spacing vs CounterPreset violated");

  // MdcEn/MdcEn_n correctness and exclusivity
  assert property (@cb MdcEn    == (CountEq0 && !Mdc))
    else $error("MdcEn definition mismatch");

  assert property (@cb MdcEn_n  == (CountEq0 &&  Mdc))
    else $error("MdcEn_n definition mismatch");

  assert property (@cb !(MdcEn && MdcEn_n))
    else $error("MdcEn and MdcEn_n both high");

  assert property (@cb (MdcEn || MdcEn_n) == CountEq0)
    else $error("MdcEn/MdcEn_n do not cover CountEq0");

  // Coverage
  cover property (@cb Reset ##1 !Reset ##1 CountEq0);                    // basic reset then first pulse
  cover property (@cb (Divider <  8'd2) ##1 CountEq0 ##1 CountEq0);      // min divider: consecutive pulses
  cover property (@cb (CounterPreset == 8'd0) && CountEq0);              // P=0 case
  cover property (@cb (CounterPreset == 8'd1) && CountEq0 |=> !CountEq0 ##1 CountEq0); // P=1 case
  cover property (@cb MdcEn);                                            // observe low-phase enable
  cover property (@cb MdcEn_n);                                          // observe high-phase enable
  cover property (@cb CountEq0 |=> $changed(Mdc));                       // Mdc toggle observed

endmodule

bind eth_clockgen eth_clockgen_sva sva_i(.*);