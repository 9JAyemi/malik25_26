// SVA for my_module (bindable)
// Place in a separate file and compile with the DUT.

`ifndef MY_MODULE_SVA_SV
`define MY_MODULE_SVA_SV

module my_module_sva;

  // Sample on any input activity (combinational DUT)
  event ev;
  always @ (A1 or A2 or A3 or B1) -> ev;
  default clocking cb @(ev); endclocking

  function automatic bit inputs_ok();
    return !$isunknown({A1,A2,A3,B1,VPWR,VGND});
  endfunction

  // Rails must be correct
  ap_rails:            assert property (VPWR === 1'b1 && VGND === 1'b0);

  // Internal nets correctness
  ap_a_and:            assert property (disable iff (!inputs_ok()) a_and === (A1 & A2 & A3));
  ap_b_not:            assert property (disable iff (!inputs_ok()) b_not === ~B1);

  // Output correctness (functional and structural)
  ap_x_func:           assert property (disable iff (!inputs_ok()) X === ((A1 & A2 & A3) & ~B1));
  ap_x_struct:         assert property (disable iff (!inputs_ok()) X === (a_and & b_not));

  // No unknown on output when inputs/rails are known
  ap_no_x_out:         assert property (disable iff (!inputs_ok()) !$isunknown(X));

  // Readable implications (redundant with ap_x_func but useful)
  ap_x_implies_inputs: assert property (disable iff (!inputs_ok()) X |-> (A1 && A2 && A3 && !B1));
  ap_b1_blocks_x:      assert property (disable iff (!inputs_ok()) B1 |-> !X);

  // Coverage: exercise all 16 input combinations
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_minterms
      cp_inputs_minterm: cover property (inputs_ok() && {A1,A2,A3,B1} == i);
    end
  endgenerate

  // Coverage: observe X transitions
  cp_x_rise:           cover property (inputs_ok() && $rose(X));
  cp_x_fall:           cover property (inputs_ok() && $fell(X));

endmodule

bind my_module my_module_sva my_module_sva_i();

`endif