// SVA checks for the given primitives. Concise, high-signal-value checks with minimal false positives.

`timescale 1ns/1ps

// ---------------- BUFG ----------------
module BUFG_sva (input I, O);
  // When O changes, it must equal I (glitch-free output value)
  property p_bufg_val_on_change;
    @(posedge O or negedge O) O == I;
  endproperty
  assert property (p_bufg_val_on_change);

  // No X/Z on O
  assert property (@(O) !$isunknown(O));

  // Coverage: see activity
  cover property (@(posedge O) 1);
  cover property (@(negedge O) 1);
endmodule
bind BUFG BUFG_sva u_bufg_sva(.I(I), .O(O));

// ---------------- BUFGMUX ----------------
module BUFGMUX_sva (input I0,I1,S,O);
  // When O changes, it must equal selected input
  property p_bufgmux_val_on_change;
    @(posedge O or negedge O) O == (S ? I1 : I0);
  endproperty
  assert property (p_bufgmux_val_on_change);

  // No X/Z on control or output
  assert property (@(S) !$isunknown(S));
  assert property (@(O) !$isunknown(O));

  // Coverage: both selections exercised, O transitions
  cover property (@(posedge O)  S);
  cover property (@(posedge O) !S);
  cover property (@(negedge O) 1);
endmodule
bind BUFGMUX BUFGMUX_sva u_bufgmux_sva(.I0(I0),.I1(I1),.S(S),.O(O));

// ---------------- DCM ----------------
module DCM_sva (input CLKIN, PSCLK, PSEN, PSINCDEC, RST, CLKFB, output CLK2X, CLK0);
  // CLK0 must reflect CLKIN on each CLK0 edge (value-correct at change time)
  assert property (@(posedge CLK0 or negedge CLK0) CLK0 == CLKIN);

  // Outputs never X/Z
  assert property (@(CLK0)  !$isunknown(CLK0));
  assert property (@(CLK2X) !$isunknown(CLK2X));

  // Coverage: observe edges on outputs
  cover property (@(posedge CLK0) 1);
  cover property (@(negedge CLK0) 1);
  cover property (@(posedge CLK2X) 1);
  cover property (@(negedge CLK2X) 1);
endmodule
bind DCM DCM_sva u_dcm_sva(.CLKIN(CLKIN),.PSCLK(PSCLK),.PSEN(PSEN),.PSINCDEC(PSINCDEC),.RST(RST),.CLKFB(CLKFB),.CLK2X(CLK2X),.CLK0(CLK0));

// ---------------- ODDR2 ----------------
module ODDR2_sva (input D0,D1,C0,C1, output Q);
  // Functional edges
  assert property (@(posedge C0) Q == D0);
  assert property (@(posedge C1) Q == D1);

  // Q changes only on C0 or C1 rising edges
  assert property (@(posedge Q or negedge Q) $rose(C0) || $rose(C1));

  // No X/Z on Q
  assert property (@(Q) !$isunknown(Q));

  // Coverage: both clock domains drive Q
  cover property (@(posedge C0) 1);
  cover property (@(posedge C1) 1);
endmodule
bind ODDR2 ODDR2_sva u_oddr2_sva(.D0(D0),.D1(D1),.C0(C0),.C1(C1),.Q(Q));

// ---------------- RAMB16_S9 ----------------
module RAMB16_S9_sva (
  input CLK, EN, SSR, WE,
  input [10:0] ADDR,
  input [7:0] DI,
  input DIP,
  output [7:0] DO,
  output DOP
);
  // Coverage: reads and writes seen
  cover property (@(posedge CLK) EN && WE);
  cover property (@(posedge CLK) EN && !WE);

  // Immediate, time-accurate checks for the #1 output latency and write-through
  // Write-through on EN&WE: after #1, output must equal written data
  always @(posedge CLK) if (EN && WE) begin
    automatic logic [8:0] w = {DIP,DI};
    fork
      begin
        #1;
        assert ({DOP,DO} == w)
          else $error("RAMB16_S9 write-through mismatch: expected %0h, got %0h", w, {DOP,DO});
      end
    join_none
  end

  // If EN==0 at a clock, outputs must not update after the #1 output latency
  always @(posedge CLK) begin
    automatic bit en_samp = EN;
    automatic logic [8:0] dout_pre = {DOP,DO};
    fork
      begin
        #1;
        if (!en_samp) begin
          assert ({DOP,DO} == dout_pre)
            else $error("RAMB16_S9 outputs changed while EN==0");
        end
      end
    join_none
  end

  // Outputs never X/Z
  assert property (@({DOP,DO}) !$isunknown({DOP,DO}));
endmodule
bind RAMB16_S9 RAMB16_S9_sva u_ramb16_s9_sva(.CLK(CLK),.EN(EN),.SSR(SSR),.WE(WE),.ADDR(ADDR),.DI(DI),.DIP(DIP),.DO(DO),.DOP(DOP));

// ---------------- RAM16X1S ----------------
module RAM16X1S_sva (
  input A0,A1,A2,A3,WCLK,WE,D, output O
);
  // On O change, it must equal current memory at selected address
  // (legal to reference internal mem/rdaddr due to bind into the module scope)
  // This checks the combinational read correctness at the time of update.
  assert property (@(posedge O or negedge O) O == mem[rdaddr]);

  // Coverage: writes happen
  cover property (@(posedge WCLK) dly_WE);

  // No X/Z on O
  assert property (@(O) !$isunknown(O));
endmodule
bind RAM16X1S RAM16X1S_sva u_ram16x1s_sva(.A0(A0),.A1(A1),.A2(A2),.A3(A3),.WCLK(WCLK),.WE(WE),.D(D),.O(O));

// ---------------- RAM16X4S ----------------
// Covered by the four RAM16X1S instances via their binds. Add light wrapper coverage.
module RAM16X4S_sva (input WCLK,WE);
  cover property (@(posedge WCLK) WE);
endmodule
bind RAM16X4S RAM16X4S_sva u_ram16x4s_sva(.WCLK(WCLK),.WE(WE));

// ---------------- SRLC16E ----------------
module SRLC16E_sva (
  input A0,A1,A2,A3,CLK,CE,D, output Q15,Q
);
  // Q must equal mem[rdaddr] whenever it changes (combinational read correctness)
  assert property (@(posedge Q or negedge Q) Q == mem[rdaddr]);

  // Q15 only changes on CLK rising edge when CE is sampled high
  assert property (@(posedge Q15 or negedge Q15) $rose(CLK) && dly_CE);

  // No X/Z on outputs
  assert property (@(Q)   !$isunknown(Q));
  assert property (@(Q15) !$isunknown(Q15));

  // Coverage: shift activity
  cover property (@(posedge CLK) dly_CE);
endmodule
bind SRLC16E SRLC16E_sva u_srlc16e_sva(.A0(A0),.A1(A1),.A2(A2),.A3(A3),.CLK(CLK),.CE(CE),.D(D),.Q15(Q15),.Q(Q));

// ---------------- MUXCY ----------------
module MUXCY_sva (input S,CI,DI, output O);
  // When O changes, it must equal the mux function
  assert property (@(posedge O or negedge O) O == (S ? CI : DI));

  // No X/Z on O, and S not X
  assert property (@(O) !$isunknown(O));
  assert property (@(S) !$isunknown(S));

  // Coverage: both data paths selected
  cover property (@(posedge O)  S);
  cover property (@(posedge O) !S);
endmodule
bind MUXCY MUXCY_sva u_muxcy_sva(.S(S),.CI(CI),.DI(DI),.O(O));