// SVA for mealy_state_machine
// Bind this file to the DUT: bind mealy_state_machine mealy_state_machine_sva sva();

module mealy_state_machine_sva;

  // Hook into DUT signals via bind (no ports needed when bound by name)
  // If your tool requires explicit ports, uncomment below and bind with connections.
  /*
  input clk, reset, in1, in2;
  input [2:0] state, next_state;
  input out1, out2;
  */

  // State encodings (match DUT)
  localparam logic [2:0] A = 3'b000, B = 3'b001, C = 3'b010, D = 3'b011, E = 3'b100;

  // Default SVA context
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Predicates
  function automatic logic [2:0] f_next (input logic [2:0] s, input logic i1, i2);
    unique case (s)
      A: f_next = (i1==0 && i2==0) ? B :
                  (i1==0 && i2==1) ? A :
                  (i1==1 && i2==0) ? D : C;
      B: f_next = (i1==0 && i2==0) ? C :
                  (i1==0 && i2==1) ? B :
                  (i1==1 && i2==0) ? E : A;
      C: f_next = (i1==0 && i2==0) ? A :
                  (i1==0 && i2==1) ? C :
                  (i1==1 && i2==0) ? B : D;
      D: f_next = (i1==0 && i2==0) ? E :
                  (i1==0 && i2==1) ? D :
                  (i1==1 && i2==0) ? C : B;
      E: f_next = E;
      default: f_next = A;
    endcase
  endfunction

  function automatic logic [1:0] f_out (input logic [2:0] s, input logic i1, i2);
    unique case (s)
      A: f_out = (i1==0 && i2==0) ? 2'b10 :
                 (i1==0 && i2==1) ? 2'b00 :
                 (i1==1 && i2==0) ? 2'b01 : 2'b11;
      B: f_out = (i1==0 && i2==0) ? 2'b01 :
                 (i1==0 && i2==1) ? 2'b00 :
                 (i1==1 && i2==0) ? 2'b10 : 2'b01;
      C: f_out = (i1==0 && i2==0) ? 2'b11 :
                 (i1==0 && i2==1) ? 2'b01 :
                 (i1==1 && i2==0) ? 2'b11 : 2'b01;
      D: f_out = (i1==0 && i2==0) ? 2'b00 :
                 (i1==0 && i2==1) ? 2'b00 :
                 (i1==1 && i2==0) ? 2'b11 : 2'b00;
      E: f_out = (i1==1 && i2==0) ? 2'b00 : 2'b10;
      default: f_out = 2'b00;
    endcase
  endfunction

  // Helper: only check when we have a valid past sample while enabled
  // Use antecedent "reset && $past(reset)" in all time-dependent checks.

  // Asynchronous reset effect observed on next clock (sanity)
  assert property (@cb (!reset) |-> (state==A && out1==0 && out2==0));

  // No X/Z when actively running (after at least 1 enabled cycle)
  assert property (@cb (reset && $past(reset)) |-> !$isunknown({state,next_state,out1,out2,in1,in2}));

  // State must be legal when running
  assert property (@cb (reset && $past(reset)) |-> (state==A || state==B || state==C || state==D || state==E));

  // SPEC: Mealy outputs = f(state,in) registered -> appear next cycle
  assert property (@cb (reset && $past(reset)) |-> {out1,out2} == f_out($past(state), $past(in1), $past(in2)));

  // Intended next-state function registered into next_state
  assert property (@cb (reset && $past(reset)) |-> next_state == f_next($past(state), $past(in1), $past(in2)));

  // Intended state update should match next-state function (will flag any mis-pipe/bug)
  assert property (@cb (reset && $past(reset)) |-> state == f_next($past(state), $past(in1), $past(in2)));

  // Implementation relationship (state follows previous next_state)
  assert property (@cb (reset && $past(reset)) |-> state == $past(next_state));

  // E must be absorbing for state (redundant with f_next, but explicit)
  assert property (@cb (reset && $past(reset) && $past(state)==E) |-> state==E);

  // --------------- Coverage ---------------

  // Visit each state
  cover property (@cb reset && state==A);
  cover property (@cb reset && state==B);
  cover property (@cb reset && state==C);
  cover property (@cb reset && state==D);
  cover property (@cb reset && state==E);

  // Exercise all input combinations in each state
  // A
  cover property (@cb reset && state==A && in1==0 && in2==0);
  cover property (@cb reset && state==A && in1==0 && in2==1);
  cover property (@cb reset && state==A && in1==1 && in2==0);
  cover property (@cb reset && state==A && in1==1 && in2==1);
  // B
  cover property (@cb reset && state==B && in1==0 && in2==0);
  cover property (@cb reset && state==B && in1==0 && in2==1);
  cover property (@cb reset && state==B && in1==1 && in2==0);
  cover property (@cb reset && state==B && in1==1 && in2==1);
  // C
  cover property (@cb reset && state==C && in1==0 && in2==0);
  cover property (@cb reset && state==C && in1==0 && in2==1);
  cover property (@cb reset && state==C && in1==1 && in2==0);
  cover property (@cb reset && state==C && in1==1 && in2==1);
  // D
  cover property (@cb reset && state==D && in1==0 && in2==0);
  cover property (@cb reset && state==D && in1==0 && in2==1);
  cover property (@cb reset && state==D && in1==1 && in2==0);
  cover property (@cb reset && state==D && in1==1 && in2==1);
  // E
  cover property (@cb reset && state==E && in1==0 && in2==0);
  cover property (@cb reset && state==E && in1==0 && in2==1);
  cover property (@cb reset && state==E && in1==1 && in2==0);
  cover property (@cb reset && state==E && in1==1 && in2==1);

  // Cover all output combinations
  cover property (@cb reset && {out1,out2}==2'b00);
  cover property (@cb reset && {out1,out2}==2'b01);
  cover property (@cb reset && {out1,out2}==2'b10);
  cover property (@cb reset && {out1,out2}==2'b11);

  // Cover taking each defined transition (state,in -> next state and outputs)
  // A transitions
  cover property (@cb reset && state==A && in1==0 && in2==0 |=> state==B && {out1,out2}==2'b10);
  cover property (@cb reset && state==A && in1==0 && in2==1 |=> state==A && {out1,out2}==2'b00);
  cover property (@cb reset && state==A && in1==1 && in2==0 |=> state==D && {out1,out2}==2'b01);
  cover property (@cb reset && state==A && in1==1 && in2==1 |=> state==C && {out1,out2}==2'b11);
  // B transitions
  cover property (@cb reset && state==B && in1==0 && in2==0 |=> state==C && {out1,out2}==2'b01);
  cover property (@cb reset && state==B && in1==0 && in2==1 |=> state==B && {out1,out2}==2'b00);
  cover property (@cb reset && state==B && in1==1 && in2==0 |=> state==E && {out1,out2}==2'b10);
  cover property (@cb reset && state==B && in1==1 && in2==1 |=> state==A && {out1,out2}==2'b01);
  // C transitions
  cover property (@cb reset && state==C && in1==0 && in2==0 |=> state==A && {out1,out2}==2'b11);
  cover property (@cb reset && state==C && in1==0 && in2==1 |=> state==C && {out1,out2}==2'b01);
  cover property (@cb reset && state==C && in1==1 && in2==0 |=> state==B && {out1,out2}==2'b11);
  cover property (@cb reset && state==C && in1==1 && in2==1 |=> state==D && {out1,out2}==2'b01);
  // D transitions
  cover property (@cb reset && state==D && in1==0 && in2==0 |=> state==E && {out1,out2}==2'b00);
  cover property (@cb reset && state==D && in1==0 && in2==1 |=> state==D && {out1,out2}==2'b00);
  cover property (@cb reset && state==D && in1==1 && in2==0 |=> state==C && {out1,out2}==2'b11);
  cover property (@cb reset && state==D && in1==1 && in2==1 |=> state==B && {out1,out2}==2'b00);
  // E transitions (self-loop)
  cover property (@cb reset && state==E && in1==0 && in2==0 |=> state==E && {out1,out2}==2'b10);
  cover property (@cb reset && state==E && in1==0 && in2==1 |=> state==E && {out1,out2}==2'b10);
  cover property (@cb reset && state==E && in1==1 && in2==0 |=> state==E && {out1,out2}==2'b00);
  cover property (@cb reset && state==E && in1==1 && in2==1 |=> state==E && {out1,out2}==2'b10);

endmodule

// Bind into the DUT
bind mealy_state_machine mealy_state_machine_sva sva();