// SVA checker for AdlerChecksum. Bind this to the DUT.
module AdlerChecksum_sva #(parameter int n = 16) ();

  // Runs on every simulation time advance
  default clocking cb @(posedge $global_clock); endclocking

  // Reference model helpers
  function automatic logic [15:0] fA(input logic [n*8-1:0] din);
    int i; int unsigned accA;
    begin
      accA = 1;
      for (i=0; i<n; i++) accA = (accA + din[i*8 +: 8]) % 65521;
      return accA[15:0];
    end
  endfunction

  function automatic logic [15:0] fB(input logic [n*8-1:0] din);
    int i; int unsigned accA, accB;
    begin
      accA = 1; accB = 1;
      for (i=0; i<n; i++) begin
        accA = (accA + din[i*8 +: 8]) % 65521;
        accB = (accB + accA) % 65521;
      end
      return accB[15:0];
    end
  endfunction

  function automatic bit wrapA(input logic [n*8-1:0] din);
    int i; int unsigned accA; bit w;
    begin
      accA = 1; w = 0;
      for (i=0; i<n; i++) begin
        int unsigned tmp = accA + din[i*8 +: 8];
        if (tmp >= 65521) w = 1;
        accA = tmp % 65521;
      end
      return w;
    end
  endfunction

  function automatic bit wrapB(input logic [n*8-1:0] din);
    int i; int unsigned accA, accB; bit w;
    begin
      accA = 1; accB = 1; w = 0;
      for (i=0; i<n; i++) begin
        accA = (accA + din[i*8 +: 8]) % 65521;
        int unsigned tmpB = accB + accA;
        if (tmpB >= 65521) w = 1;
        accB = tmpB % 65521;
      end
      return w;
    end
  endfunction

  // Assertions (access DUT signals directly via bind scope)
  ap_out_func: assert property (out == fA(in));
  ap_A_func:   assert property (A   == fA(in));
  ap_B_func:   assert property (B   == fB(in));

  ap_ranges:   assert property (A < 16'd65521 && B < 16'd65521);

  // Out truncates to A given 16-bit out
  ap_out_eq_A: assert property (out == A);

  // Error definition
  ap_err_def:  assert property (error === (out != check));

  // No X/Z on outputs/internals when inputs are known
  ap_no_x:     assert property (!$isunknown({in,check}) |-> !$isunknown({out,error,A,B}));

  // Coverage
  cp_match:    cover property ($changed({in,check}) && (out == check));
  cp_mismatch: cover property ($changed({in,check}) && (out != check));
  cp_wrapA:    cover property ($changed(in) && wrapA(in));
  cp_wrapB:    cover property ($changed(in) && wrapB(in));

endmodule

// Bind into the DUT
bind AdlerChecksum AdlerChecksum_sva #(.n(n)) u_adler_sva();