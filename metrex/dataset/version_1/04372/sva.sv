// SVA for module lfsr
// Bind to the DUT to access internal Lfsr
module lfsr_sva (
  input logic        Clk,
  input logic        Reset,
  input logic        Enable,
  input logic [15:0] Data,
  input logic        Done,
  input logic [15:0] Lfsr
);

  default clocking cb @(posedge Clk); endclocking

  // Reset behavior (asynchronous in RTL, observed next clock due to #Tp)
  a_reset_effect_next: assert property ( $past(Reset) |-> (Lfsr==16'h0 && Data==16'h0 && Done==1'b0) );
  a_reset_held_zeros:  assert property (  Reset && $past(Reset) |-> (Lfsr==16'h0 && Data==16'h0 && Done==1'b0) );

  // Update on enable (one-cycle-late checks due to #Tp)
  a_lfsr_next: assert property (
    !$past(Reset) && $past(Enable)
    |-> Lfsr == { $past(Lfsr[14:0]),
                  $past(Lfsr[0]) ^ $past(Lfsr[2]) ^ $past(Lfsr[3]) ^ $past(Lfsr[5]) }
  );

  a_data_next: assert property ( !$past(Reset) && $past(Enable) |-> Data == $past(Lfsr) );

  // Hold when idle
  a_hold_idle: assert property (
    !$past(Reset) && !$past(Enable)
    |-> Lfsr == $past(Lfsr) && Data == $past(Data) && Done == 1'b0
  );

  // Done follows Enable (one-cycle-late)
  a_done_next_from_en: assert property ( !$past(Reset) |-> Done == $past(Enable) );
  a_done_next_from_rst: assert property (  $past(Reset) |-> Done == 1'b0 );

  // No X/Z on outputs after reset deasserted
  a_no_x: assert property ( !$isunknown({Lfsr, Data, Done}) ) disable iff (Reset);

  // Stuck-zero characteristic from zero state under this tap set
  a_zero_lock: assert property ( $past(Enable) && ($past(Lfsr)==16'h0) |-> (Lfsr==16'h0 && Data==16'h0) );

  // Coverage
  c_reset_then_update: cover property ( $fell(Reset) ##1 Enable );
  c_two_updates:       cover property ( $fell(Reset) ##1 Enable ##1 Enable );
  c_idle_hold:         cover property ( !$past(Reset) && !$past(Enable)
                                        && Lfsr==$past(Lfsr) && Data==$past(Data) && Done==1'b0 );

endmodule

bind lfsr lfsr_sva u_lfsr_sva(.Clk(Clk), .Reset(Reset), .Enable(Enable), .Data(Data), .Done(Done), .Lfsr(Lfsr));