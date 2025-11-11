// SVA checker for module buffer
// Focus: functional correctness, X-propagation sanity, and coverage

module buffer_sva (
  input VPWR,
  input VGND,
  input Z,
  input A,
  input TE_B
);

  // Derived condition: power-good when VPWR==1 and VGND==0 (4-state exact)
  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Sample on any relevant input edge
  localparam int unsigned DUMMY = 0; // keep tools happy in empty else branches
  // Functional equivalence: Z must equal TE_B & VPWR & !VGND (4-state aware)
  property p_func;
    @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge TE_B or negedge TE_B)
      Z === (TE_B ? (VPWR & !VGND) : 1'b0);
  endproperty
  assert property (p_func)
    else $error("buffer: Z must equal (TE_B ? (VPWR & !VGND) : 1'b0)");

  // When power is good, Z mirrors TE_B; when not, Z must be 0
  property p_power_good_maps_to_teb;
    @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge TE_B or negedge TE_B)
      power_good |-> (Z === TE_B);
  endproperty
  assert property (p_power_good_maps_to_teb)
    else $error("buffer: with power_good, Z must equal TE_B");

  property p_power_bad_forces_zero;
    @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge TE_B or negedge TE_B)
      (!power_good) |-> (Z === 1'b0);
  endproperty
  assert property (p_power_bad_forces_zero)
    else $error("buffer: without power_good, Z must be 0");

  // No X on Z when controlling inputs are known (binary-clean inputs -> binary-clean output)
  property p_no_x_when_inputs_known;
    @(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge TE_B or negedge TE_B)
      (!$isunknown({VPWR, VGND, TE_B})) |-> (!$isunknown(Z));
  endproperty
  assert property (p_no_x_when_inputs_known)
    else $error("buffer: Z is X/Z while VPWR,VGND,TE_B are known");

  // A has no functional influence in this implementation: changing A alone must not change Z
  property p_a_independent;
    @(posedge A or negedge A)
      $stable({VPWR, VGND, TE_B}) |-> (Z == $past(Z));
  endproperty
  assert property (p_a_independent)
    else $error("buffer: Z changed due to A while VPWR/VGND/TE_B were stable");

  // ----------------------------------
  // Coverage
  // ----------------------------------
  // Gate enable drives Z high when power-good
  cover property (@(posedge TE_B) power_good && (Z === 1'b1));
  // Gate disable forces Z low
  cover property (@(negedge TE_B) (Z === 1'b0));
  // Power-up with enable already high drives Z high
  cover property (@(posedge VPWR) (VGND === 1'b0) && (TE_B === 1'b1) && (Z === 1'b1));
  // Losing power_good forces Z low
  cover property (@(posedge VGND) (VPWR === 1'b1) && (TE_B === 1'b1) && (Z === 1'b0));
  // Exercise A toggling with no effect on Z
  cover property (@(posedge A or negedge A) $stable({VPWR, VGND, TE_B}) && $stable(Z));

endmodule

// Bind the checker to every instance of buffer
bind buffer buffer_sva buffer_sva_i (.*);