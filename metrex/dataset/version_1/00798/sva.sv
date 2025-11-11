// SVA for waveform_generator
module waveform_generator_sva(
  input logic A1,
  input logic A2,
  input logic B1,
  input logic Y,
  input logic Y_internal
);

  // Clock for sequential checks
  default clocking cb @(posedge B1); endclocking

  // Combinational A21O (as implemented) must always hold on any input change
  property a21oi_func_p;
    @(posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1)
      Y_internal === ((A1 & A2) | B1);
  endproperty
  assert property (a21oi_func_p);

  // Y registers Y_internal (sampled previous edge in SVA sampling semantics)
  property y_captures_yint_p;
    1 |=> (Y == $past(Y_internal));
  endproperty
  assert property (y_captures_yint_p);

  // Y changes only on a rising edge of B1
  assert property (@(posedge Y or negedge Y) $rose(B1));

  // No X at sampling and after update
  assert property ( !$isunknown({A1,A2,B1,Y_internal}) );
  assert property ( 1 |=> !$isunknown(Y) );

  // Coverage
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );
  cover property ( Y==1 );
  cover property ( Y==0 );

  // Partitioned functional coverage of input space
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) (B1==1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) (B1==0 && A1==0 && A2==0));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) (B1==0 && (A1^A2)==1));
  cover property (@(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1) (B1==0 && A1==1 && A2==1));

endmodule

// Bind into the DUT (captures internal Y_internal as well)
bind waveform_generator waveform_generator_sva u_waveform_generator_sva (
  .A1(A1),
  .A2(A2),
  .B1(B1),
  .Y(Y),
  .Y_internal(Y_internal)
);