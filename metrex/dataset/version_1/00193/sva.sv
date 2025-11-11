// SVA for wifi_tx. Bind this file to the DUT.
// Focus: combinational I/Q mapping, phase sequencing, and mod_signal_out encoding.

module wifi_tx_sva;
  // Will be bound into wifi_tx instance; uses its scope signals.
  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] neg4(input logic [3:0] v);
    neg4 = -v;
  endfunction

  // Combinational mapping checks (sampled on clk for simplicity)
  // For data_in[7:6]==00: I=data_in[5:3], Q=data_in[2:0]; else default 0.
  property p_map;
    !$isunknown(data_in) |-> ##0 (
      (data_in[7:6]==2'b00 && I=={1'b0,data_in[5:3]} && Q=={1'b0,data_in[2:0]}) ||
      (data_in[7:6]!=2'b00 && I==4'd0 && Q==4'd0)
    );
  endproperty
  assert property (p_map) else $error("I/Q mapping incorrect");

  // I,Q always 0..7 and known
  assert property (##0 (I[3]==1'b0 && Q[3]==1'b0 && !$isunknown({I,Q}))))
    else $error("I/Q out of range or X/Z");

  // Phase sequencing (only when known)
  assert property (disable iff ($isunknown(phase)) (phase==2'b00 |=> phase==2'b01))
    else $error("Phase 00->01 sequence error");
  assert property (disable iff ($isunknown(phase)) (phase==2'b01 |=> phase==2'b10))
    else $error("Phase 01->10 sequence error");
  assert property (disable iff ($isunknown(phase)) (phase==2'b10 |=> phase==2'b11))
    else $error("Phase 10->11 sequence error");
  assert property (disable iff ($isunknown(phase)) (phase==2'b11 |=> phase==2'b00))
    else $error("Phase 11->00 sequence error");

  // mod_signal_out encoding per phase.
  // Use ##0 so we check after procedural updates at this clock edge.
  assert property (disable iff ($isunknown(phase)) (1 |-> ##0 mod_signal_out[15:8]==8'h00))
    else $error("Upper 8 bits of mod_signal_out must be zero");
  assert property (disable iff ($isunknown(phase))
                   (phase==2'b00 |-> ##0 (mod_signal_out[7:4]==I        && mod_signal_out[3:0]==Q)))
    else $error("Phase 00 output mismatch");
  assert property (disable iff ($isunknown(phase))
                   (phase==2'b01 |-> ##0 (mod_signal_out[7:4]==I        && mod_signal_out[3:0]==neg4(Q))))
    else $error("Phase 01 output mismatch");
  assert property (disable iff ($isunknown(phase))
                   (phase==2'b10 |-> ##0 (mod_signal_out[7:4]==neg4(I)  && mod_signal_out[3:0]==neg4(Q))))
    else $error("Phase 10 output mismatch");
  assert property (disable iff ($isunknown(phase))
                   (phase==2'b11 |-> ##0 (mod_signal_out[7:4]==neg4(I)  && mod_signal_out[3:0]==Q)))
    else $error("Phase 11 output mismatch");

  // Coverage: phase cycle, default branch hit, max I/Q, and a negative quadrant observed.
  cover property (phase==2'b00 ##1 phase==2'b01 ##1 phase==2'b10 ##1 phase==2'b11 ##1 phase==2'b00);
  cover property (data_in[7:6]!=2'b00 && I==0 && Q==0);
  cover property (data_in==8'h3F && I==4'd7 && Q==4'd7);
  cover property (phase==2'b10 && (I!=0 || Q!=0) ##0
                  (mod_signal_out[7] || mod_signal_out[3])); // observe negative nibbles
endmodule

bind wifi_tx wifi_tx_sva u_wifi_tx_sva();