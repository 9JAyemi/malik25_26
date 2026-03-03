// SVA for sky130_fd_sc_ls__einvp (notif1: Z = ~A when TE==1, else Z = 'z)

module sky130_fd_sc_ls__einvp_sva (
  input logic Z,
  input logic A,
  input logic TE
);

  // Functional checks (combinational, race-safe via immediate asserts)
  always @* begin
    if (TE === 1'b1) begin
      assert (Z === ~A)
        else $error("einvp SVA: TE=1 => Z must be ~A (A=%b Z=%b)", A, Z);
    end else if (TE === 1'b0) begin
      assert (Z === 1'bz)
        else $error("einvp SVA: TE=0 => Z must be Z (Z=%b)", Z);
    end
  end

  // X-propagation when enabled
  always @* if (TE === 1'b1 && $isunknown(A)) begin
    assert ($isunknown(Z))
      else $error("einvp SVA: TE=1 and A unknown => Z must be unknown (A=%b Z=%b)", A, Z);
  end

  // Sanity: when enabled with known A, Z must be a known 0/1 (not X/Z)
  always @* if (TE === 1'b1 && (A===1'b0 || A===1'b1)) begin
    assert (!$isunknown(Z) && Z !== 1'bz)
      else $error("einvp SVA: TE=1 and A known => Z must be 0/1 (Z=%b)", Z);
  end

  // Coverage: exercise all meaningful modes and edges
  default clocking cb @(posedge TE or negedge TE or posedge A or negedge A); endclocking

  // Steady-state coverage
  cover property (TE===1'b0 && Z===1'bz);
  cover property (TE===1'b1 && A===1'b0 && Z===1'b1);
  cover property (TE===1'b1 && A===1'b1 && Z===1'b0);

  // Enable/disable edges
  cover property ($rose(TE) && A===1'b0 && Z===1'b1);
  cover property ($rose(TE) && A===1'b1 && Z===1'b0);
  cover property ($fell(TE) && Z===1'bz);

  // Data toggles while enabled
  cover property ($rose(A) && TE===1'b1 && Z===1'b0);
  cover property ($fell(A) && TE===1'b1 && Z===1'b1);

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__einvp sky130_fd_sc_ls__einvp_sva u_sva (.Z(Z), .A(A), .TE(TE));