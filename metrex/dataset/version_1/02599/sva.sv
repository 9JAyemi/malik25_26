// SVA checker for sky130_fd_sc_ms__xor3 (X = ~(A ^ B ^ C))
module sky130_fd_sc_ms__xor3_sva #(parameter bit ENABLE_COVERAGE = 1) (
  input logic A, B, C, X
);

  // Sample on any input edge; evaluate consequents after ##0 to avoid race with combinational updates
  default clocking cb @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C); endclocking

  // Functional correctness when inputs are known
  property p_func;
    !$isunknown({A,B,C}) |-> ##0 (X === ~(A ^ B ^ C));
  endproperty
  assert property (p_func)
    else $error("sky130_fd_sc_ms__xor3: X != ~(A^B^C)");

  // Output toggle parity equals input toggle parity (robust dynamic check)
  property p_toggle_parity;
    !$isunknown({A,B,C,$past(A),$past(B),$past(C),X,$past(X)}) |-> ##0
      ((X ^ $past(X)) === ((A ^ $past(A)) ^ (B ^ $past(B)) ^ (C ^ $past(C))));
  endproperty
  assert property (p_toggle_parity)
    else $error("sky130_fd_sc_ms__xor3: toggle parity mismatch");

  // Coverage
  if (ENABLE_COVERAGE) begin
    // Hit all 8 input combinations
    genvar i;
    for (i = 0; i < 8; i++) begin : cov_inputs
      cover property (##0 {A,B,C} == i[2:0]);
    end
    // Single-bit toggle causes X to toggle
    cover property (
      !$isunknown({A,B,C,$past(A),$past(B),$past(C),X,$past(X)}) &&
      $onehot({A^$past(A), B^$past(B), C^$past(C)}) ##0 (X ^ $past(X))
    );
    // Two-bit toggle keeps X stable
    cover property (
      !$isunknown({A,B,C,$past(A),$past(B),$past(C),X,$past(X)}) &&
      ($countones({A^$past(A), B^$past(B), C^$past(C)}) == 2) ##0 (X == $past(X))
    );
  end
endmodule

// Bind the checker to the DUT
bind sky130_fd_sc_ms__xor3 sky130_fd_sc_ms__xor3_sva u_sky130_fd_sc_ms__xor3_sva (.A(A), .B(B), .C(C), .X(X));