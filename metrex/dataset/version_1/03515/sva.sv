// SVA for FSM
// Bind with: bind FSM FSM_sva i_FSM_sva(.*);

module FSM_sva(
  input [31:0] x, y, z, k, kappa_LUTRot, theta_LUTRot, delta_LUTRot,
  input [31:0] kappa_LUTVec, theta_LUTVec, delta_LUTVec,
  input [31:0] theta_LUT, kappa_LUT, delta_LUT,
  input [1:0]  mode,
  input        operation, clock,
  input        done_LUTRot, done_LUTVec, done_LUT,
  input        done_ALU,
  output reg   enable_LUT,
  output reg [7:0]  address,
  output reg [31:0] theta_out, kappa_out, delta_out,
  output reg        done_FSM,
  output reg [31:0] x_final, y_final, z_final, k_final,
  input  [7:0]      exponent,
  input             converge
);

  default clocking cb @(posedge clock); endclocking

  // past-valid for safe $past usage (no explicit reset in DUT)
  bit past_valid;
  always @(posedge clock) past_valid <= 1'b1;

  // Helpers
  wire done_any = done_LUT | done_LUTRot | done_LUTVec;

  // Basic X/Z checks on controls
  assert property (past_valid |-> !$isunknown({operation, mode, enable_LUT, done_LUT, done_LUTRot, done_LUTVec, done_ALU})));

  // Exponent combinational calculation
  assert property (operation == 1'b1 |-> exponent == (8'h7F - z[30:23]));
  assert property (operation == 1'b0 |-> exponent == (x[30:23] - y[30:23]));

  // When LUT returns while enabled: clear enable; done_FSM set unless done_ALU overrides
  assert property (enable_LUT && done_any |-> !enable_LUT && (done_ALU ? (done_FSM == 1'b0) : (done_FSM == 1'b1)));

  // Address/stability while waiting for LUT
  assert property (enable_LUT && !done_any |-> $stable(address));
  assert property (enable_LUT |-> !$isunknown(address)));

  // Handshake result formatting (op==0, mode==00 or exp in mid-range): replace exponent field only; kappa_out stable
  assert property ( enable_LUT && done_any && operation==1'b0
                    && (mode==2'b00 || (exponent <= 8'hF3 && exponent > 8'h80)) && !done_ALU
                    |-> delta_out[30:23] == (exponent + 8'h7F)
                     && delta_out[22:0]  == delta_LUT[22:0]
                     && delta_out[31]    == delta_LUT[31]
                     && theta_out[30:23] == (exponent + 8'h7F)
                     && theta_out[22:0]  == theta_LUT[22:0]
                     && theta_out[31]    == theta_LUT[31]
                     && $stable(kappa_out) );

  // Handshake result formatting (op==1 -> ROT LUT)
  assert property ( enable_LUT && done_any && operation==1'b1 && !done_ALU
                    |-> theta_out[31]    == ~z[31]
                     && delta_out[31]    == ~z[31]
                     && theta_out[30:0]  == theta_LUTRot[30:0]
                     && delta_out[30:0]  == delta_LUTRot[30:0]
                     && kappa_out        == kappa_LUTRot );

  // Handshake result formatting (op==0 -> VEC LUT)
  assert property ( enable_LUT && done_any && operation==1'b0
                    && !(mode==2'b00 || (exponent <= 8'hF3 && exponent > 8'h80)) && !done_ALU
                    |-> theta_out == theta_LUTVec
                     && delta_out == delta_LUTVec
                     && kappa_out == kappa_LUTVec );

  // done_ALU always clears done_FSM the same cycle
  assert property (done_ALU |-> done_FSM == 1'b0);

  // Operation==1 paths
  // Converge + final registers latch
  assert property (operation==1'b1 && z[30:23] <= 8'h70
                   |-> converge==1'b1
                    && x_final==x && y_final==y && z_final==z && k_final==k);

  // Mode==00 immediate result
  assert property (operation==1'b1 && z[30:23] > 8'h70 && mode==2'b00 && !done_ALU
                   |-> theta_out[30:0]==z[30:0] && delta_out[30:0]==z[30:0]
                    && theta_out[31]==~z[31] && delta_out[31]==~z[31]
                    && kappa_out==32'h3F800000 && done_FSM==1'b1);

  // Saturation for mode==11
  assert property (operation==1'b1 && mode==2'b11 && z[30:23] >= 8'h7F && !done_ALU
                   |-> theta_out==32'hBF800000 && delta_out==32'hBF42F7D6
                    && kappa_out==32'h3FC583AB && done_FSM==1'b1);

  // Saturation for mode==01
  assert property (operation==1'b1 && mode==2'b01 && z[30:23] >= 8'h7F && !done_ALU
                   |-> theta_out==32'hBF800000 && delta_out==32'hBFC75923
                    && kappa_out==32'h3FECE788 && done_FSM==1'b1);

  // LUT request (mid exp range)
  assert property (operation==1'b1 && mode!=2'b00 && (z[30:23] < 8'h7F) && (z[30:23] > 8'h73)
                   |-> enable_LUT==1'b1
                    && address[7:4]==exponent[3:0]
                    && address[3:0]==z[22:19]);

  // Small exp fallback (same as mode==00)
  assert property (operation==1'b1 && mode!=2'b00 && z[30:23] <= 8'h73 && !done_ALU
                   |-> theta_out[30:0]==z[30:0] && delta_out[30:0]==z[30:0]
                    && theta_out[31]==~z[31] && delta_out[31]==~z[31]
                    && kappa_out==32'h3F800000 && done_FSM==1'b1);

  // Operation==0 paths
  // Converge only
  assert property (operation==1'b0 && z[30:23] <= 8'h70 |-> converge==1'b1);

  // Mode==00 -> LUT address + kappa preset
  assert property (operation==1'b0 && mode==2'b00 && z[30:23] > 8'h70
                   |-> address[7:4]==x[22:19] && address[3:0]==y[22:19]
                    && kappa_out==32'h000003F8 && enable_LUT==1'b1);

  // mode!=00, very large exponent -> alt address format
  assert property (operation==1'b0 && mode!=2'b00 && (exponent > 8'hF3) && (exponent <= 8'hFF)
                   |-> address[7:4]==exponent[3:0]
                    && address[3:2]==x[22:21] && address[1:0]==y[22:21]
                    && enable_LUT==1'b1);

  // mode!=00, mid exponent -> full nibbles + kappa preset
  assert property (operation==1'b0 && mode!=2'b00 && (exponent <= 8'hF3) && (exponent > 8'h80)
                   |-> address[7:4]==x[22:19] && address[3:0]==y[22:19]
                    && kappa_out==32'h000003F8 && enable_LUT==1'b1);

  // Low exponent, mode==11 constants
  assert property (operation==1'b0 && mode==2'b11 && exponent <= 8'h80 && !done_ALU
                   |-> delta_out==32'h3F733333 && theta_out==32'h3FEA77CB
                    && kappa_out==32'h3E9FDF38 && done_FSM==1'b1);

  // Low exponent, mode==01 constants
  assert property (operation==1'b0 && mode==2'b01 && exponent <= 8'h80 && !done_ALU
                   |-> delta_out==32'h000003F8 && theta_out==32'h3F490FDB
                    && kappa_out==32'h3FB504F4 && done_FSM==1'b1);

  // Liveness: when we request LUT, we eventually see a done within a bound
  parameter int MAX_LUT_LAT = 64;
  assert property ($rose(enable_LUT) |-> ##[1:MAX_LUT_LAT] done_any);

  // -------------- Coverage (key scenarios) --------------
  cover property (operation==1'b1 && z[30:23] <= 8'h70 && converge);
  cover property (operation==1'b1 && mode==2'b00 && z[30:23] > 8'h70 && done_FSM);
  cover property (operation==1'b1 && mode!=2'b00 && z[30:23] > 8'h73 && z[30:23] < 8'h7F && $rose(enable_LUT));
  cover property (operation==1'b1 && mode==2'b11 && z[30:23] >= 8'h7F && done_FSM);
  cover property (operation==1'b0 && mode==2'b00 && $rose(enable_LUT));
  cover property (operation==1'b0 && mode!=2'b00 && exponent > 8'hF3 && $rose(enable_LUT));
  cover property (operation==1'b0 && mode!=2'b00 && exponent <= 8'hF3 && exponent > 8'h80 && $rose(enable_LUT));
  cover property (enable_LUT && done_any && !done_ALU && done_FSM); // LUT completion without ALU override
  cover property (enable_LUT && done_any && done_ALU && !done_FSM); // ALU overrides done_FSM

endmodule