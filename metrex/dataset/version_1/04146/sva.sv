// SVA for sky130_fd_sc_ls__dlrbp
// Bind-in, concise, checks full Boolean function, power, and key invariants + coverage

module sky130_fd_sc_ls__dlrbp_sva (
  input  logic RESET_B,
  input  logic D,
  input  logic VPWR,
  input  logic VGND,
  input  logic VPB,
  input  logic VNB,
  input  logic GATE,
  input  logic Q,
  input  logic Q_N,
  input  logic D_N,
  input  logic Q_PRE
);

  function automatic bit power_good;
    return (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  endfunction

  // Functional correctness (combinational)
  always @* if (power_good()) begin
    assert (D_N   === ~D)                            else $error("D_N != ~D");
    assert (Q_PRE === ~(D_N & RESET_B & GATE))       else $error("Q_PRE mismatch");
    assert (Q_N   === ~(D   & RESET_B & GATE))       else $error("Q_N mismatch");
    assert (Q     === Q_PRE)                         else $error("Q != Q_PRE");
    assert (!(~Q & ~Q_N))                            else $error("Q and Q_N both low");
    if (!$isunknown({D,RESET_B,GATE})) assert (!$isunknown({Q,Q_N})) else $error("Outputs X/Z with known inputs");
  end

  // Lightweight functional coverage
  default clocking cb @(
    posedge D or negedge D or
    posedge GATE or negedge GATE or
    posedge RESET_B or negedge RESET_B
  ); endclocking

  // Enabled, D=0/1
  cover property (power_good() && RESET_B && GATE && (D==1'b0) && (Q==1'b0) && (Q_N==1'b1));
  cover property (power_good() && RESET_B && GATE && (D==1'b1) && (Q==1'b1) && (Q_N==1'b0));

  // Disabled via GATE low; disabled via RESET_B low
  cover property (power_good() && RESET_B && !GATE && (Q==1'b1) && (Q_N==1'b1));
  cover property (power_good() && !RESET_B           && (Q==1'b1) && (Q_N==1'b1));

  // Q follows D when enabled
  cover property (@(posedge D)  power_good() && RESET_B && GATE && Q && !Q_N);
  cover property (@(negedge D)  power_good() && RESET_B && GATE && !Q && Q_N);

endmodule

bind sky130_fd_sc_ls__dlrbp sky130_fd_sc_ls__dlrbp_sva (.*);